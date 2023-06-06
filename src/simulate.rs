use std::collections::HashMap;

use crate::{
  chain::chain_rule,
  rules::{
    apply_rules, prove_rule, AffineVar, Config, ConsumeGrow, ReadShift, Rule,
    RuleProof::DirectSimulation, Rulebook, TapeCount, Var,
  },
  tape::{ExpTape, Signature, StepResult::*},
  turing::{Dir, Phase, SmallBinMachine, State, TapeSymbol, Turing, HALT},
};
use defaultmap::{defaulthashmap, DefaultHashMap};
use either::Either::{self, Left, Right};
use itertools::{zip_eq, Itertools};
use std::cmp::Ordering::*;

pub enum RuleStepResult<P, C> {
  VarInfinite(Var),
  RSRInfinite,
  RFellOffTape(P, Dir),
  RSuccess(P, HashMap<Var, C>, Either<ReadShift, ConsumeGrow<C>>),
}
use RuleStepResult::*;

pub fn one_rule_step<P: Phase, S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<P, S>,
  exptape: &mut ExpTape<S, C>,
  state: P,
  rulebook: &Rulebook<P, S>,
  step: u32,
  verbose: bool,
) -> RuleStepResult<P, C> {
  let (new_state, hm, rs) = match apply_rules(exptape, state, rulebook, false) {
    Some(Left(var)) => return VarInfinite(var),
    Some(Right((state, tc, cg))) => {
      if verbose {
        println!("rule_applied");
      }
      (state, tc, Right(cg))
    }
    None => match exptape.step_extra_info(state, machine) {
      UndefinedEdge(_edge) => unreachable!("machine is defined"),
      SRInfinite => return RSRInfinite,
      FellOffTape(state, dir, step) => return RFellOffTape(state, dir),
      Success(state, rs, step) => (state, HashMap::default(), Left(rs)),
    },
  };
  if verbose {
    println!("step: {} phase: {} tape: {}", step, new_state, exptape);
  }
  return RSuccess(new_state, hm, rs);
}

pub fn simulate_using_rules<P: Phase, S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<P, S>,
  num_steps: u32,
  rulebook: &Rulebook<P, S>,
  verbose: bool,
) -> (P, u32, ExpTape<S, C>) {
  let mut exptape = ExpTape::new(true);
  let mut state = P::START;
  for step in 1..num_steps + 1 {
    state = match one_rule_step(machine, &mut exptape, state, rulebook, step, verbose) {
      VarInfinite(_var) => return (P::INFINITE, step, exptape),
      RSRInfinite => return (P::INFINITE, step, exptape),
      RFellOffTape(_, _) => panic!("fell off tape unexpectedly"),
      RSuccess(state, _, _) => state,
    };
    if state.halted() {
      return (state, step, exptape);
    }
    // println!("step: {} phase: {} tape: {}", step, state, exptape);
  }
  return (state, num_steps, exptape);
}

fn collate<S: TapeSymbol>(
  (f_sym, f_num): (S, u32),
  (s_sym, s_num): (S, u32),
) -> ((S, AffineVar), (S, AffineVar), bool) {
  // bool is was there a var used
  assert_eq!(f_sym, s_sym);
  match f_num.cmp(&s_num) {
    Less => (
      (f_sym, AffineVar { n: 0, a: 1, var: Var(0) }),
      (
        s_sym,
        AffineVar {
          n: s_num.checked_sub(f_num).expect("we used cmp"),
          a: 1,
          var: Var(0),
        },
      ),
      true,
    ),
    Equal => (
      (f_sym, AffineVar::constant(f_num)),
      (s_sym, AffineVar::constant(s_num)),
      false,
    ),
    Greater => (
      (
        f_sym,
        AffineVar {
          n: f_num.checked_sub(s_num).expect("we used cmp"),
          a: 1,
          var: Var(0),
        },
      ),
      (s_sym, AffineVar { n: 0, a: 1, var: Var(0) }),
      true,
    ),
  }
}

fn collate2<S: TapeSymbol>(
  pairs: &[((S, u32), (S, u32))],
) -> Option<((S, AffineVar), (S, AffineVar), bool)> {
  todo!()
  // // bool is was there a var used
  // assert_eq!(f_sym, s_sym);
  // match f_num.cmp(&s_num) {
  //   Less => (
  //     (f_sym, AffineVar { n: 0, a: 1, var: Var(0) }),
  //     (
  //       s_sym,
  //       AffineVar {
  //         n: s_num.checked_sub(f_num).expect("we used cmp"),
  //         a: 1,
  //         var: Var(0),
  //       },
  //     ),
  //     true,
  //   ),
  //   Equal => (
  //     (f_sym, AffineVar::constant(f_num)),
  //     (s_sym, AffineVar::constant(s_num)),
  //     false,
  //   ),
  //   Greater => (
  //     (
  //       f_sym,
  //       AffineVar {
  //         n: f_num.checked_sub(s_num).expect("we used cmp"),
  //         a: 1,
  //         var: Var(0),
  //       },
  //     ),
  //     (s_sym, AffineVar { n: 0, a: 1, var: Var(0) }),
  //     true,
  //   ),
  // }
}

fn get_n_rle<S: TapeSymbol>(slice: &[(S, u32)], n: u32) -> Vec<(S, u32)> {
  //gets the last n things from an RLE encoded slice
  let mut num_take = 0;
  let mut current_taken = 0;
  loop {
    if num_take == slice.len() {
      break;
    }
    let (_s, next_int) = slice[(slice.len() - 1) - num_take];
    if current_taken + next_int > n {
      break;
    } else {
      num_take += 1;
      current_taken += next_int;
    }
  }
  let mut out = vec![];
  if current_taken < n {
    if num_take == slice.len() {
      out.push((S::empty(), n - current_taken));
    } else {
      let (s, next_int) = slice[(slice.len() - 1) - num_take];
      assert!(next_int > n - current_taken);
      out.push((s, n - current_taken));
    }
  }
  for i in 0..num_take {
    out.push(slice[slice.len() - num_take + i])
  }
  assert_eq!(n, out.iter().map(|(_, n)| n).sum());
  out
}

fn cut_exptape<S: TapeSymbol>(
  ExpTape { left, head, right, tape_end_inf }: &ExpTape<S, u32>,
  l: i32,
  r: i32,
) -> ExpTape<S, u32> {
  assert!(tape_end_inf);
  assert!(l <= 0, "l should be > 0 {}", l);
  let l_cut = (-1 * l).try_into().unwrap();
  let new_left = get_n_rle(&left, l_cut);

  assert!(r >= 0, "r should be > 0 {}", r);
  let r_cut = r.try_into().unwrap();
  let new_right = get_n_rle(right, r_cut);

  ExpTape {
    left: new_left,
    head: *head,
    right: new_right,
    tape_end_inf: false,
  }
}

fn conforms_to_linear(m: u32, b: i32, (x, y): (u32, u32)) -> bool {
  return i32::try_from(y).unwrap() == i32::try_from(m * x).unwrap() + b;
}

fn i32f(x: u32) -> i32 {
  x.try_into().unwrap()
}

fn u32f(x: i32) -> u32 {
  x.try_into().unwrap()
}

fn detect_linear_relation(pairs: &[(u32, u32)]) -> Option<(AffineVar, AffineVar)> {
  // pairs has to be at least length 2, or we panic
  // if y = mx + b then m = y_2 - y_1 / (x_2 - x_1) and b = y_1 - mx_1
  let (x_1, y_1) = pairs[0];
  let (x_2, y_2) = pairs[1];
  let rise = i32f(y_2) - i32f(y_1);
  let run = i32f(x_2) - i32f(x_1);
  //todo run == 0
  if rise % run != 0 {
    return None;
  }
  let m = rise / run;
  let m = if m < 0 {
    return None;
  } else if m == 0 {
    // maybe revisit?
    return None;
  } else {
    u32f(m)
  };

  //todo m == 0
  let b: i32 = i32::try_from(y_1).unwrap() - i32::try_from(m * x_1).unwrap();
  if !pairs.iter().all(|&pair| conforms_to_linear(m, b, pair)) {
    return None;
  }
  if b >= 0 {
    Some((
      AffineVar { n: 0, a: 1, var: Var(0) },
      AffineVar { n: b.try_into().unwrap(), a: m, var: Var(0) },
    ))
  } else {
    let neg_b: u32 = (-b).try_into().unwrap();
    let c = neg_b.div_ceil(m); // c >= -b/m => mc + b >= 0
    let k = m * c - neg_b; // positive by previous
    Some((
      AffineVar { n: c, a: 1, var: Var(0) },
      AffineVar { n: k, a: m, var: Var(0) },
    ))
  }
}

fn make_side<S: TapeSymbol>(
  start: &[(S, u32)],
  end: &[(S, u32)],
) -> (Vec<(S, AffineVar)>, Vec<(S, AffineVar)>, bool) {
  let (start_idx, end_idx) = match start.len().cmp(&end.len()) {
    Less => (0, end.len() - start.len()),
    Equal => (0, 0),
    Greater => (start.len() - end.len(), 0),
  };

  let mut start_out = start[0..start_idx]
    .into_iter()
    .map(|&(s, n)| (s, n.into()))
    .collect_vec();
  let mut end_out = end[0..end_idx]
    .into_iter()
    .map(|&(s, n)| (s, n.into()))
    .collect_vec();

  let mut var_used = false;
  for (&s, &e) in zip_eq(&start[start_idx..], &end[end_idx..]) {
    let (s_var, e_var, was_var) = collate(s, e);
    var_used = var_used || was_var;
    start_out.push(s_var);
    end_out.push(e_var);
  }
  (start_out, end_out, var_used)
}

fn make_side2<S: TapeSymbol>(
  pairs: &[(&[(S, u32)], &[(S, u32)])],
) -> Option<(Vec<(S, AffineVar)>, Vec<(S, AffineVar)>)> {
  let first_in_len = pairs[0].0.len();
  let first_out_len = pairs[0].1.len();
  // check everyone is the same length
  if !pairs
    .iter()
    .all(|(in_slice, out_slice)| (in_slice.len(), out_slice.len()) == (first_in_len, first_out_len))
  {
    return None;
  }

  let (start_idx, end_idx) = match first_in_len.cmp(&first_out_len) {
    Less => (0, first_out_len - first_in_len),
    Equal => (0, 0),
    Greater => (first_in_len - first_out_len, 0),
  };
  // check everyone has the same "tail"
  let start_tail = &pairs[0].0[0..start_idx];
  let end_tail = &pairs[0].1[0..end_idx];
  if !pairs.iter().all(|&(in_slice, out_slice)| {
    (&in_slice[0..start_idx], &out_slice[0..end_idx]) == (start_tail, end_tail)
  }) {
    return None;
  }

  let mut start_out: Vec<(S, AffineVar)> = start_tail
    .into_iter()
    .map(|&(s, n)| (s, n.into()))
    .collect_vec();
  let mut end_out: Vec<(S, AffineVar)> = end_tail
    .into_iter()
    .map(|&(s, n)| (s, n.into()))
    .collect_vec();

  for (in_ind, out_ind) in zip_eq(start_idx..first_in_len, end_idx..first_out_len) {
    let sym_num_pairs = pairs
      .iter()
      .map(|(in_slice, out_slice)| (in_slice[in_ind], out_slice[out_ind]))
      .collect_vec();
    let (s_ans, e_ans, _was_var) = collate2(&sym_num_pairs)?;
    start_out.push(s_ans);
    end_out.push(e_ans);
  }

  Some((start_out, end_out))
}

pub fn detect_rule<P: Phase, S: TapeSymbol>(
  (phase_in, et_in): (P, ExpTape<S, u32>),
  (phase_out, et_out): (P, ExpTape<S, u32>),
  verbose: bool,
) -> Vec<Rule<P, S>> {
  if verbose {
    println!("detecting rule from\n{}\nto\n{}", &et_in, &et_out);
  }

  let ExpTape {
    left: end_left_in,
    head: end_head,
    right: end_right_in,
    tape_end_inf: _,
  } = et_out;
  let ExpTape {
    left: start_left_in,
    head: start_head,
    right: start_right_in,
    tape_end_inf: _,
  } = et_in;
  assert_eq!(start_head, end_head);

  let (start_left, end_left, _var_used_left) = make_side(&start_left_in, &end_left_in);
  let (start_right, end_right, _var_used_right) = make_side(&start_right_in, &end_right_in);
  // if !var_used_left && !var_used_right {
  //   return vec![];
  // }
  let rule = Rule {
    start: Config {
      state: phase_in,
      left: start_left,
      head: start_head,
      right: start_right,
    },
    end: Config::new_from_avars(phase_out, end_left, end_head, end_right),
  };
  vec![rule]
}

fn detect_rule2<P: Phase, S: TapeSymbol>(
  config_pairs: &[((P, ExpTape<S, u32>), (P, ExpTape<S, u32>))],
) -> Option<Rule<P, S>> {
  // all phases everywhere the same
  let first_phase_pair = (config_pairs[0].0 .0, config_pairs[0].1 .0);
  assert_eq!(first_phase_pair.0, first_phase_pair.1);
  assert!(config_pairs
    .iter()
    .all(|((p1, _), (p2, _))| (*p1, *p2) == first_phase_pair));

  // all heads everywhere the same
  let first_head_pair = (config_pairs[0].0 .1.head, config_pairs[0].1 .1.head);
  assert_eq!(first_head_pair.0, first_head_pair.1);
  assert!(config_pairs
    .iter()
    .all(|((_, et_in), (_, et_out))| (et_in.head, et_out.head) == first_head_pair));

  // make sides
  let lefts = config_pairs
    .iter()
    .map(|((_, et_in), (_, et_out))| (et_in.left.as_slice(), et_out.left.as_slice()))
    .collect_vec();
  let (left_in, left_out) = make_side2(&lefts)?;

  let rights = config_pairs
    .iter()
    .map(|((_, et_in), (_, et_out))| (et_in.right.as_slice(), et_out.right.as_slice()))
    .collect_vec();
  let (right_in, right_out) = make_side2(&rights)?;

  // construct rule
  Some(Rule {
    start: Config {
      state: first_phase_pair.0,
      left: left_in,
      head: first_head_pair.0,
      right: right_in,
    },
    end: Config::new_from_avars(first_phase_pair.0, left_out, first_head_pair.0, right_out),
  })
}

pub fn make_example_from_history<P: Phase, S: TapeSymbol>(
  history: &[(u32, P, ExpTape<S, u32>)],
  readshifts: &[ReadShift],
  start_ind: usize,
  end_ind: usize,
) -> ((P, ExpTape<S, u32>), (P, ExpTape<S, u32>)) {
  let start_step = history[start_ind].0 as usize;
  let end_step = history[end_ind].0 as usize;
  let readshift_range = &readshifts[start_step..end_step];
  let rs @ ReadShift { l, r, s } = ReadShift::normalize(ReadShift::combine_many(readshift_range));

  assert!(l <= 0, "{:?}", rs);
  assert!(r >= 0, "{:?}", rs);
  let start = &history[start_ind];
  let et_in = cut_exptape(&start.2, l, r);

  let end = &history[end_ind];
  let et_out = cut_exptape(&end.2, l - s, r - s);

  ((start.1, et_in), (end.1, et_out))
}

pub fn last_n_config_pairs<P: Phase, S: TapeSymbol>(
  history: &[(u32, P, ExpTape<S, u32>)],
  readshifts: &[ReadShift],
  n: usize,
) -> Vec<((P, ExpTape<S, u32>), (P, ExpTape<S, u32>))> {
  let mut out = vec![];
  let hist_len = history.len();
  for i in 0..n {
    out.push(make_example_from_history(
      history,
      readshifts,
      hist_len - (1 + i),
      hist_len - (2 + i),
    ));
  }
  out
}

pub fn detect_rules<P: Phase, S: TapeSymbol>(
  step: u32,
  state: P,
  exptape: &ExpTape<S, u32>,
  signatures: &mut DefaultHashMap<(P, Signature<S>), Vec<(u32, P, ExpTape<S, u32>)>>,
  readshifts: &[ReadShift],
  verbose: bool,
) -> Vec<Rule<P, S>> {
  let cur_sig_vec = &mut signatures[(state, exptape.signature())];
  cur_sig_vec.push((step, state, exptape.clone()));
  if cur_sig_vec.len() > 2 {
    let config_pairs = last_n_config_pairs(cur_sig_vec, readshifts, 2);
    let mb_rule = detect_rule2(&config_pairs);
  }

  if cur_sig_vec.len() > 1 {
    let start_ind = cur_sig_vec.len() - 2;
    let end_ind = cur_sig_vec.len() - 1;

    let (config_in, config_out) =
      make_example_from_history(cur_sig_vec, readshifts, start_ind, end_ind);
    let rules = detect_rule(config_in, config_out, false);
    if rules.len() > 0 && verbose {
      println!(
        "using steps: {:?} detected rule:\n{}\n",
        cur_sig_vec.iter().map(|(s, _, _)| s).collect_vec(),
        rules.first().unwrap()
      );
    }
    return rules;
  }

  return vec![];
}

pub fn proving_rules_step<P: Phase, S: TapeSymbol>(
  machine: &impl Turing<P, S>,
  step: u32,
  mut state: P,
  exptape: &mut ExpTape<S, u32>,
  rulebook: &mut Rulebook<P, S>,
  signatures: &mut DefaultHashMap<(P, Signature<S>), Vec<(u32, P, ExpTape<S, u32>)>>,
  readshifts: &mut Vec<ReadShift>,
  verbose: bool,
) -> P {
  if verbose {
    // println!("\nstarting step {}", step);
  }

  let (new_state, _hm, cg_or_rs) =
    match one_rule_step(machine, exptape, state, rulebook, step, verbose) {
      VarInfinite(_var) => {
        if verbose {
          println!("proved machine runs forever using a rule");
        }
        return P::INFINITE;
      }
      RSRInfinite => {
        if verbose {
          println!("proved machine runs forever using a trans");
        }
        return P::INFINITE;
      }
      RSuccess(new_state, hm, cg_or_rs) => (new_state, hm, cg_or_rs),
      RFellOffTape(_, _) => panic!("unexpectedly fell off tape"),
    };
  state = new_state;

  let readshift = cg_or_rs.either(|rs| rs, |cg| ReadShift::rs_from_cg(cg));
  if verbose {
    // println!("rs: {:?}", readshift);
  }
  readshifts.push(readshift);

  if state.halted() {
    return state;
  }

  let rules = detect_rules(step, state, &exptape, signatures, &readshifts, false);
  for rule in rules {
    if let Some((final_rule, pf)) = prove_rule(machine, rule, rulebook, 50, -5, false) {
      if pf != DirectSimulation(1) {
        if let Some(chained_rule) = chain_rule(&final_rule) {
          if verbose {
            println!("proved rule:\n{}\nvia proof{:?}", final_rule, pf);
          }
          if verbose {
            println!("chained the proved rule to:\n{}", chained_rule);
          }
          rulebook.add_rule(chained_rule);
        } else {
          if verbose {
            println!(
              "proved rule:\n{}\nvia proof{:?}\nbut could not chain",
              final_rule, pf
            );
          }
        }
        // rulebook.add_rule(final_rule);
      }
    }
  }
  state
}

pub fn simulate_proving_rules<P: Phase, S: TapeSymbol>(
  machine: &impl Turing<P, S>,
  num_steps: u32,
  rulebook: &mut Rulebook<P, S>,
  verbose: bool,
) -> (P, u32) {
  /*
  the plan to detect rules:
  store the signatures of everything seen so far
  if you see the same signature more than once, there is a possible rule
  */
  let mut exptape = ExpTape::new(true);
  let mut state = P::START;
  let mut signatures: DefaultHashMap<(P, Signature<S>), Vec<(u32, P, ExpTape<S, u32>)>> =
    defaulthashmap!();
  let mut readshifts = vec![];
  for step in 1..num_steps + 1 {
    state = proving_rules_step(
      machine,
      step,
      state,
      &mut exptape,
      rulebook,
      &mut signatures,
      &mut readshifts,
      verbose,
    );
    if state == P::INFINITE || state.halted() {
      return (state, step);
    }
    if exptape.numbers_too_large() {
      //put cond about u32s
      println!(
        "warning! gave up on machine {} due to simulating to\nstep: {} phase: {} tape: {}",
        machine.to_compact_format(),
        step,
        state,
        exptape
      );
      return (state, step);
    }
  }
  return (state, num_steps);
}

pub fn aggregate_and_display_proving_res(results: &Vec<(SmallBinMachine, State, u32)>) {
  let mut halt_count = 0;
  let mut inf_count = 0;
  let mut inconclusive_count = 0;
  for (_m, state, _steps) in results {
    match *state {
      HALT => halt_count += 1,
      State::INFINITE => inf_count += 1,
      _ => inconclusive_count += 1,
    }
  }
  println!(
    "halted: {} infinite: {} inconclusive: {}",
    halt_count, inf_count, inconclusive_count
  );
}

pub fn aggregate_and_display_macro_proving_res<const N: usize>(
  results: &Vec<(SmallBinMachine, State, u32, usize)>,
) {
  let mut halt_count = 0;
  let mut inf_counts: [u32; N] = [0; N];
  let mut inconclusive_count = 0;
  for (_m, state, _steps, macro_size) in results {
    match *state {
      HALT => halt_count += 1,
      State::INFINITE => inf_counts[*macro_size - 1] += 1,
      _ => inconclusive_count += 1,
    }
  }
  let total_infinite: u32 = inf_counts.iter().sum();
  println!(
    "halted: {} infinite: {} inconclusive: {}\ninf_counts: {:?}",
    halt_count, total_infinite, inconclusive_count, inf_counts,
  );
}

#[cfg(test)]
mod test {

  use crate::{
    parse::{parse_avar, parse_exact, parse_tape_side},
    turing_examples::undecided_size_3,
  };

  use super::*;

  fn simultaneous_step_prove_step<P: Phase, S: TapeSymbol>(
    machine: &impl Turing<P, S>,
    step: u32,
    normal_tape: &mut ExpTape<S, u32>,
    mut normal_state: P,
    rule_tape: &mut ExpTape<S, u32>,
    rule_state: P,
    rulebook: &mut Rulebook<P, S>,
    signatures: &mut DefaultHashMap<(P, Signature<S>), Vec<(u32, P, ExpTape<S, u32>)>>,
    readshifts: &mut Vec<ReadShift>,
    verbose: bool,
  ) -> Option<(P, P)> {
    assert_eq!(normal_state, rule_state);
    assert_eq!(normal_tape, rule_tape);
    let new_rule_state = proving_rules_step(
      machine, step, rule_state, rule_tape, rulebook, signatures, readshifts, verbose,
    );
    if new_rule_state == P::INFINITE {
      return None;
    }

    let mut num_steps_to_match = 0;

    while (new_rule_state, &mut *rule_tape) != (normal_state, normal_tape) {
      if num_steps_to_match > 300 || normal_state.halted() {
        panic!(
          "machine diverged:\n{} {}\nvs\n{} {}",
          new_rule_state, rule_tape, normal_state, normal_tape
        );
      }
      normal_state = normal_tape
        .step_extra_info(normal_state, machine)
        .expect_success()
        .0;
      num_steps_to_match += 1;
    }
    return Some((normal_state, new_rule_state));
  }

  fn compare_machine_with_proving_rules<P: Phase, S: TapeSymbol>(
    machine: &impl Turing<P, S>,
    num_steps: u32,
  ) {
    let mut normal_tape = ExpTape::new(true);
    let mut normal_state = P::START;
    let mut rule_tape = ExpTape::new(true);
    let mut rule_state = P::START;
    let mut rulebook = Rulebook::chain_rulebook(machine);
    let mut signatures: DefaultHashMap<(P, Signature<S>), Vec<(u32, P, ExpTape<S, u32>)>> =
      defaulthashmap!();
    let mut readshifts = vec![];
    for step in 1..num_steps + 1 {
      (normal_state, rule_state) = match simultaneous_step_prove_step(
        machine,
        step,
        &mut normal_tape,
        normal_state,
        &mut rule_tape,
        rule_state,
        &mut rulebook,
        &mut signatures,
        &mut readshifts,
        true,
      ) {
        Some(ans) => ans,
        None => return,
      };
    }
  }

  #[test]
  fn prove_rules_is_same_as_not() {
    for m_str in undecided_size_3() {
      println!("working on machine: {}", m_str);
      let machine = SmallBinMachine::from_compact_format(m_str);
      compare_machine_with_proving_rules(&machine, 100);
    }
  }

  #[test]
  fn get_n_rle_test() {
    let tape_half = parse_exact(parse_tape_side("(T, 3) (F, 5) (T, 1) (F, 6) (T, 2)"));

    let ans1 = parse_exact(parse_tape_side("(F, 6) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 8), ans1);

    let ans1 = parse_exact(parse_tape_side("(F, 5) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 7), ans1);

    let ans1 = parse_exact(parse_tape_side("(F, 1) (T, 1) (F, 6) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 10), ans1);

    let ans1 = parse_exact(parse_tape_side("(F, 3) (T, 3) (F, 5) (T, 1) (F, 6) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 20), ans1);
  }

  fn detect_linear_relation_driver(pairs: &[(u32, u32)], ans: Option<(&str, &str)>) {
    let ans = ans.map(|(l, r)| (parse_exact(parse_avar(l)), parse_exact(parse_avar(r))));
    assert_eq!(detect_linear_relation(pairs), ans);
  }
  #[test]
  fn detect_linear_relation_test() {
    // x + 2
    let pairs = [(3, 5), (4, 6)];
    detect_linear_relation_driver(&pairs, Some(("0 + 1*x_0", "2 + 1*x_0")));

    let wrong_pairs = [(3, 5), (4, 6), (5, 7), (6, 9)];
    detect_linear_relation_driver(&wrong_pairs, None);

    // 3x + 5
    let pairs = [(2, 11), (8, 29)];
    detect_linear_relation_driver(&pairs, Some(("0 + 1*x_0", "5 + 3*x_0")));

    // x - 7
    let pairs = [(11, 4), (8, 1)];
    detect_linear_relation_driver(&pairs, Some(("7 + 1*x_0", "0 + 1*x_0")));

    // 3x - 5
    let pairs = [(2, 1), (5, 10), (4, 7)];
    detect_linear_relation_driver(&pairs, Some(("2 + 1*x_0", "1 + 3*x_0")));

    // run = 0
    let pairs = [(3, 7), (3, 7)];

    // m = 0
    let pairs = [(4, 7), (5, 7)];
    detect_linear_relation_driver(&pairs, None);
  }
}
