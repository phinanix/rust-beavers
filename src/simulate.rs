use std::collections::HashMap;

use crate::{
  chain::chain_rule,
  rules::{
    apply_rules, prove_rule, AffineVar, Config, ConsumeGrow, ReadShift, Rule,
    RuleProof::DirectSimulation, Rulebook, TapeCount, Var,
  },
  tape::{ExpTape, Signature, StepResult::*},
  turing::{Dir, SmallBinMachine, State, TapeSymbol, Turing, HALT, INFINITE, START},
};
use defaultmap::{defaulthashmap, DefaultHashMap};
use either::Either::{self, Left, Right};
use itertools::{zip_eq, Itertools};
use std::cmp::Ordering::*;

pub enum RuleStepResult<C> {
  VarInfinite(Var),
  RFellOffTape(Dir),
  RSuccess(State, HashMap<Var, C>, Either<ReadShift, ConsumeGrow<C>>),
}
use RuleStepResult::*;

pub fn one_rule_step<S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<S>,
  exptape: &mut ExpTape<S, C>,
  state: State,
  rulebook: &Rulebook<S>,
  step: u32,
  verbose: bool,
) -> RuleStepResult<C> {
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
      FellOffTape(dir) => return RFellOffTape(dir),
      Success(state, rs) => (state, HashMap::default(), Left(rs)),
    },
  };
  if verbose {
    println!("step: {} phase: {} tape: {}", step, new_state, exptape);
  }
  return RSuccess(new_state, hm, rs);
}

pub fn simulate_using_rules<S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<S>,
  num_steps: u32,
  rulebook: &Rulebook<S>,
  verbose: bool,
) -> (State, u32, ExpTape<S, C>) {
  let mut exptape = ExpTape::new(true);
  let mut state = START;
  for step in 1..num_steps + 1 {
    state = match one_rule_step(machine, &mut exptape, state, rulebook, step, verbose) {
      VarInfinite(_var) => return (INFINITE, step, exptape),
      RFellOffTape(_) => panic!("fell off tape unexpectedly"),
      RSuccess(state, _, _) => state,
    };
    if state == HALT {
      return (HALT, step, exptape);
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

fn make_side<S: TapeSymbol>(
  start: &Vec<(S, u32)>,
  end: &Vec<(S, u32)>,
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

pub fn detect_rule<S: TapeSymbol>(
  history: &Vec<(u32, State, ExpTape<S, u32>)>,
  rs: ReadShift,
  verbose: bool,
) -> Vec<Rule<S>> {
  /* we're detecting an additive rule, so any numbers that don't change, we guess don't change
  and any numbers that do change, we guess change by that constant each time
  so we need to
  1) make vectors of the change amount
  2) zip those vectors with the signatures and turn them into configs
  */
  let ReadShift { l, r, s } = ReadShift::normalize(rs);

  assert!(l <= 0, "{:?}", rs);
  assert!(r >= 0, "{:?}", rs);
  let second_last = &history[history.len() - 2];
  let et_in = cut_exptape(&second_last.2, l, r);

  let last = &history[history.len() - 1];
  if verbose {
    println!(
      "detecting rule from step {} to step {}",
      second_last.0, last.0
    );
  }
  let et_out = cut_exptape(&last.2, l - s, r - s);

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
  let (start_left, end_left, _var_used_left) = make_side(&start_left_in, &end_left_in);
  let (start_right, end_right, _var_used_right) = make_side(&start_right_in, &end_right_in);
  // if !var_used_left && !var_used_right {
  //   return vec![];
  // }
  let rule = Rule {
    start: Config {
      state: second_last.1,
      left: start_left,
      head: start_head,
      right: start_right,
    },
    end: Config::new_from_avars(last.1, end_left, end_head, end_right),
  };
  vec![rule]
}

pub fn detect_rules<S: TapeSymbol>(
  step: u32,
  state: State,
  exptape: &ExpTape<S, u32>,
  signatures: &mut DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>>,
  readshifts: &Vec<ReadShift>,
  verbose: bool,
) -> Vec<Rule<S>> {
  let cur_sig_vec = &mut signatures[(state, exptape.signature())];
  cur_sig_vec.push((step, state, exptape.clone()));
  if cur_sig_vec.len() > 1 {
    let steps = cur_sig_vec.iter().map(|(s, _, _)| s).collect_vec();
    let second_last_step = *steps[steps.len() - 2] as usize;
    let last_step = *steps[steps.len() - 1] as usize;
    let readshift_range = &readshifts[second_last_step..last_step];
    let readshift = ReadShift::combine_many(readshift_range);
    if verbose {
      println!("detection rs: {:?}", readshift);
    }
    let rules = detect_rule(cur_sig_vec, readshift, false);
    if rules.len() > 0 && verbose {
      println!(
        "using steps: {:?} detected rule:\n{}\n",
        steps,
        rules.first().unwrap()
      );
    }
    return rules;
  }
  return vec![];
}

pub fn proving_rules_step<S: TapeSymbol>(
  machine: &impl Turing<S>,
  step: u32,
  mut state: State,
  exptape: &mut ExpTape<S, u32>,
  rulebook: &mut Rulebook<S>,
  signatures: &mut DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>>,
  readshifts: &mut Vec<ReadShift>,
  verbose: bool,
) -> State {
  if verbose {
    // println!("\nstarting step {}", step);
  }

  let (new_state, _hm, cg_or_rs) =
    match one_rule_step(machine, exptape, state, rulebook, step, verbose) {
      VarInfinite(_var) => {
        if verbose {
          println!("proved machine runs forever using a rule");
        }
        return INFINITE;
      }
      RSuccess(new_state, hm, cg_or_rs) => (new_state, hm, cg_or_rs),
      RFellOffTape(_) => panic!("unexpectedly fell off tape"),
    };
  state = new_state;

  let readshift = cg_or_rs.either(|rs| rs, |cg| ReadShift::rs_from_cg(cg));
  if verbose {
    // println!("rs: {:?}", readshift);
  }
  readshifts.push(readshift);

  if state == HALT {
    return HALT;
  }

  let rules = detect_rules(step, state, &exptape, signatures, &readshifts, false);
  for rule in rules {
    if let Some((final_rule, pf)) = prove_rule(machine, rule, rulebook, 20, -5, false) {
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

pub fn simulate_proving_rules<S: TapeSymbol>(
  machine: &impl Turing<S>,
  num_steps: u32,
  rulebook: &mut Rulebook<S>,
  verbose: bool,
) -> (State, u32) {
  /*
  the plan to detect rules:
  store the signatures of everything seen so far
  if you see the same signature more than once, there is a possible rule
  */
  let mut exptape = ExpTape::new(true);
  let mut state = START;
  let mut signatures: DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>> =
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
    if state == INFINITE || state == HALT {
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
      INFINITE => inf_count += 1,
      _ => inconclusive_count += 1,
    }
  }
  println!(
    "halted: {} infinite: {} inconclusive: {}",
    halt_count, inf_count, inconclusive_count
  );
}

mod test {

  use crate::{
    parse::{parse_exact, parse_tape_side},
    turing_examples::undecided_size_3,
  };

  use super::*;

  fn simultaneous_step_prove_step<S: TapeSymbol>(
    machine: &impl Turing<S>,
    step: u32,
    normal_tape: &mut ExpTape<S, u32>,
    mut normal_state: State,
    rule_tape: &mut ExpTape<S, u32>,
    rule_state: State,
    rulebook: &mut Rulebook<S>,
    signatures: &mut DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>>,
    readshifts: &mut Vec<ReadShift>,
    verbose: bool,
  ) -> Option<(State, State)> {
    assert_eq!(normal_state, rule_state);
    assert_eq!(normal_tape, rule_tape);
    let new_rule_state = proving_rules_step(
      machine, step, rule_state, rule_tape, rulebook, signatures, readshifts, verbose,
    );
    if new_rule_state == INFINITE {
      return None;
    }

    let mut num_steps_to_match = 0;

    while (new_rule_state, &mut *rule_tape) != (normal_state, normal_tape) {
      if num_steps_to_match > 300 || normal_state == HALT {
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

  fn compare_machine_with_proving_rules<S: TapeSymbol>(machine: &impl Turing<S>, num_steps: u32) {
    let mut normal_tape = ExpTape::new(true);
    let mut normal_state = START;
    let mut rule_tape = ExpTape::new(true);
    let mut rule_state = START;
    let mut rulebook = Rulebook::chain_rulebook(machine);
    let mut signatures: DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>> =
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
}
