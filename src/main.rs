#![allow(dead_code)]
#![allow(unused_imports)]
#![feature(return_position_impl_trait_in_trait)]
#![feature(int_roundings)]

use std::{collections::HashSet, fs};

use crate::{
  brady::{difference_of, split_and_filter_records, Record},
  linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult},
  macro_machines::MacroMachine,
  rules::{detect_chain_rules, Rulebook},
  simulate::{aggregate_and_display_proving_res, simulate_proving_rules},
  tape::{disp_list_bit, ExpTape, Tape},
  turing::{Dir, Phase, State, HALT},
  turing_examples::get_machine,
};
use brady::{find_records, get_rs_hist_for_machine};
use either::Either::{Left, Right};
use itertools::Itertools;
use macro_machines::MacroState;
use rand::prelude::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use simulate::aggregate_and_display_macro_proving_res;
use tape::tnf_simulate;
use turing::{Bit, SmallBinMachine, Turing};
use turing_examples::{bouncers, decideable_by_macro, undecided_size_4_random_100};

mod brady;
mod chain;
mod linrecur;
mod macro_machines;
mod parse;
mod rules;
mod simulate;
mod tape;
mod turing;
mod turing_examples;

/*
to prove tail eating dragon:
- detect rules that are more than additive (mx + b?)

high level todo:
- when you guess a rule, assert that it is conserving
- chain rules which decrease by 2 or more
- rules which consume part of end are probably broken (should maybe emit ConsumedEnd)
- prove rules by induction
- detect counter rules
- chain rules which deal with modular conditions
- macro machines, or tape compression
- detect rules by repeats of transitions/rules used, rather than by tape repeating
- implicit end of tape -> explicit (?)
- track step count of rules
- heuristics based on tape growth
- bit packed tape?
- parallelize bb5 search?
*/

/* lower level todo 21 Apr 23
1) test rule prover works on any other machine
2) test rule prover works on a machine that needs a "second level" rule (a rule to prove a rule)
3) detect when a rule runs forever (using iterate_rule)
4) mb fix proving same rule more than once
5) scan tm3 and tm4 (mb tm5)
6) counters / rule induction
7) fixed size macro machines
 */

/*
rule proving status: it "mostly" "works"
current issues that need fixing:
1) it tries to prove the same rule over and over, which is obviously a big waste of time
2) relatedly, it doesn't know when a rule means it can run forever, so we need to detect that

musings on rules (1 may 23)
some rules are "necessary", most obviously anything made by chaining - in that we can't necessarily prove anything without using them
other rules are not, so maybe we just drop them?
 */

/*
todo 21 aug 23
* record records and history as we simulate
* implement heuristics based on records
* implement bouncer detector
* implement counter detector
 */

fn machines_to_str(machines: Vec<SmallBinMachine>) -> String {
  machines
    .into_iter()
    .map(|m| m.to_compact_format())
    .join("\n")
}

fn strs_to_machine(m_strs: Vec<&str>) -> Vec<SmallBinMachine> {
  m_strs
    .into_iter()
    .map(|m_str| SmallBinMachine::from_compact_format(m_str))
    .collect_vec()
}

fn dump_machines_to_file(machines: Vec<SmallBinMachine>, filename: &str) -> std::io::Result<()> {
  let machine_len = machines.len();
  let big_str = machines_to_str(machines);
  fs::write(filename, big_str)?;
  println!("wrote {} machines to file: {}", machine_len, filename);
  Ok(())
}

fn search_for_translated_cyclers(
  first_machine: &SmallBinMachine,
  num_steps: u32,
) -> Vec<(SmallBinMachine, LRResult)> {
  let machines = tnf_simulate(first_machine.clone(), 130);
  dbg!(machines.len());
  let mut lr_results = vec![];
  for m in machines {
    // let m_str = SmallBinMachine::to_compact_format(&m);
    let lr_res = lr_simulate(&m, num_steps);
    let (final_state, normal_num_steps, _tape) = Tape::simulate_from_start(&m, num_steps, false);
    lr_results.push((m, lr_res));

    // println!("m: {}, res: {:?}", m_str, lr_res);
    match lr_res {
      LRResult::Halt { num_steps: lr_num_steps } => {
        assert_eq!((final_state, normal_num_steps), (Right(HALT), lr_num_steps))
      }
      _ => (),
    }
    match final_state {
      Right(HALT) => assert_eq!(lr_res, LRResult::Halt { num_steps: normal_num_steps }),
      _ => (),
    }
  }
  aggregate_and_display_lr_res(lr_results.iter().map(|(_m, res)| *res).collect());
  lr_results
}

fn run_machine(machine: &SmallBinMachine) {
  println!("\nrunning machine: {}", machine.to_compact_format());
  let chain_rules = detect_chain_rules(machine);
  println!("{} chain rules:", chain_rules.len());
  for (i, chain_rule) in chain_rules.iter().enumerate() {
    println!("{}: {}", i, chain_rule);
  }
  println!();

  let mut rulebook = Rulebook::new(machine.num_states());
  rulebook.add_rules(chain_rules);
  let num_steps = 85;
  Tape::simulate_from_start(machine, num_steps * 3, true);
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  // println!("using rules");
  // simulate_using_rules::<Bit, u32>(machine, num_steps, &rulebook, true);
  println!("\n\nproving rules");
  simulate_proving_rules(machine, num_steps, &mut rulebook, true);
}

fn disp_records(machine: &SmallBinMachine) {
  println!(
    "\nrunning records of machine: {}",
    machine.to_compact_format()
  );

  let num_steps = 200;
  Tape::simulate_from_start(machine, num_steps, true);

  let (hist, rs) = match get_rs_hist_for_machine(machine, 200, false) {
    Left(i) => {
      println!("infinite at {i} steps");
      return;
    }
    Right((hist, rs)) => (hist, rs),
  };
  let records = find_records(&rs);
  println!("found {} records", records.len());
  // println!("\nleft");
  // for record in records.iter() {
  //   if record.2 == Dir::L {
  //     println!("{record}");
  //   }
  // }
  // println!("\nright");
  // for record in records.iter() {
  //   if record.2 == Dir::R {
  //     println!("{record}");
  //   }
  // }
  let (left_records, right_records) = split_and_filter_records(records);
  println!("\nfiltered left");

  process_records(left_records);
  println!("\nfiltered right");
  process_records(right_records.clone());

  /* goal: extract |Z| in X Z^n Y
    strategy: look at the filtered right records, take the difference of their tape extents
    hope the last 3 agree
  */
  let mut tape_extents = vec![];
  for Record(r_step, _, _) in right_records.iter() {
    let (step, phase, tape) = &hist[*r_step];
    let tape_extent = tape.len();
    tape_extents.push(tape_extent);
    println!(
      "rstep: {} step: {} phase: {} tape: {} tape extent: {} ",
      r_step, step, phase, tape, tape_extent
    );
  }
  let tape_diffs = difference_of(&tape_extents);
  println!("tape extents: {:?}", tape_extents);
  println!("tape diffs  : {:?}", tape_diffs);
  let mb_len_z = match &tape_diffs[..] {
    [.., d, e, f] => {
      if d == e && e == f {
        Some(*d as usize)
      } else {
        None
      }
    }
    _ => None,
  };
  println!("mb len z: {:?}", mb_len_z);
  let len_z: usize = match mb_len_z {
    None => {
      println!("couldn't find a len for z");
      return;
    }
    Some(len_z) => len_z,
  };
  let last_record = right_records.last().unwrap();
  let (_, last_phase, last_tape) = &hist[last_record.0];
  let last_tape_len = last_tape.len() as usize;
  let rem_last_tape_len = last_tape_len - 4 * len_z;
  let len_x = rem_last_tape_len.div_floor(2);
  let len_y = rem_last_tape_len.div_ceil(2);
  assert_eq!(len_x + len_y + 4 * len_z, last_tape_len);
  let last_tape_list: Vec<Bit> = ExpTape::to_tape(last_tape).to_list();
  let x = &last_tape_list[0..len_x];
  let y = &last_tape_list[(last_tape_list.len() - len_y)..];
  let z4 = &last_tape_list[len_x..len_x + 4 * len_z];

  assert_eq!(z4.len(), (len_z * 4) as usize);
  let mut zs = vec![];
  for i in 0..=3 {
    zs.push(&z4[i * len_z..(i + 1) * len_z]);
  }
  let z = match &zs[..] {
    [a, b, c, d] => {
      if a == b && b == c && c == d {
        a
      } else {
        println!("failed to extract z from z4: {:?} and zs: {:?}", z4, zs);
        return;
      }
    }
    _ => panic!("zs was not length 4"),
  };
  println!(
    "extracted x y z from tape:\n{}\ntapelist:\n{}\nx: {} y: {} z: {}",
    last_tape,
    disp_list_bit(&last_tape_list),
    disp_list_bit(x),
    disp_list_bit(y),
    disp_list_bit(z),
  );
}

fn process_records(records: Vec<Record>) {
  if records.len() < 3 {
    println!("records was short: {:?}", records);
    return;
  }
  // for record in records.iter() {
  //   println!("{record}");
  // }
  let steps = records.iter().map(|Record(s, _, _)| *s).collect_vec();
  let d1 = difference_of(&steps);
  let d2 = difference_of(&d1);
  println!("steps: {:?}", steps);
  println!("d1   : {:?}", d1);
  println!("d2   : {:?}", d2);
}

fn run_machine_macro<const N: usize>(machine: &SmallBinMachine) {
  println!(
    "\nrunning machine: {}\nat macro size: {}",
    machine.to_compact_format(),
    N
  );
  let macro_machine: MacroMachine<_, _, N> = MacroMachine::new(machine.clone());
  let chain_rules = detect_chain_rules(&macro_machine);
  println!("{} chain rules:", chain_rules.len());
  for (i, chain_rule) in chain_rules.iter().enumerate() {
    println!("{}: {}", i, chain_rule);
  }
  println!();

  let mut rulebook = Rulebook::new(macro_machine.num_states());
  rulebook.add_rules(chain_rules);
  let num_steps = 30;
  Tape::simulate_from_start(machine, num_steps, true);
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  // println!("using rules");
  // simulate_using_rules::<Bit, u32>(machine, num_steps, &rulebook, true);
  println!("\n\nproving rules");
  simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, true);
}

fn get_undecided(res: Vec<(SmallBinMachine, LRResult)>) -> Vec<SmallBinMachine> {
  let verbose = true;
  res
    .into_iter()
    .filter_map(|(m, r)| match r {
      LRResult::Inconclusive { steps_simulated: _ } => Some(m),
      _ => None,
    })
    .flat_map(|m| {
      let ans = m.determinize_machine();
      if verbose && !(ans.len() == 1 || ans.len() == 32) {
        println!(
          "{} -> {} {:?}",
          m.to_compact_format(),
          ans.len(),
          ans.iter().map(|m| m.to_compact_format()).collect_vec()
        )
      }
      ans
    })
    .collect_vec()
}

fn prove_with_rules(
  machines: Vec<SmallBinMachine>,
  num_steps: u32,
  verbose: bool,
) -> Vec<SmallBinMachine> {
  let mut results = vec![];
  for machine in machines {
    // println!("working on machine {}", machine.to_compact_format());
    let mut rulebook = Rulebook::chain_rulebook(&machine);
    let (new_state, steps) = simulate_proving_rules(&machine, num_steps, &mut rulebook, false);
    if new_state == State::INFINITE && verbose {
      println!("\n{}", machine.to_compact_format());
      simulate_proving_rules(
        &machine,
        num_steps,
        &mut Rulebook::chain_rulebook(&machine),
        true,
      );
    }
    results.push((machine, new_state, steps));
  }
  aggregate_and_display_proving_res(&results);
  results
    .into_iter()
    .filter_map(|(m, s, _steps)| {
      if s != State::INFINITE && s != HALT {
        Some(m)
      } else {
        None
      }
    })
    .collect_vec()
}

fn prove_macro_size<const N: usize>(
  machines: Vec<SmallBinMachine>,
  num_steps: u32,
  results: &mut Vec<(SmallBinMachine, State, u32, usize)>,
  _verbose: bool,
) -> Vec<SmallBinMachine> {
  let mut out = vec![];
  for machine in machines {
    let macro_machine: MacroMachine<State, Bit, N> = MacroMachine::new(machine.clone());
    let mut rulebook = Rulebook::chain_rulebook(&macro_machine);
    let (new_state, steps) =
      simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, false);
    if new_state == MacroState::INFINITE || new_state.halted() {
      results.push((machine, new_state.get_state(), steps, N));
    } else {
      out.push(machine);
    }
  }
  out
}

fn prove_with_macros(
  machines: Vec<SmallBinMachine>,
  num_steps: u32,
  verbose: bool,
) -> Vec<SmallBinMachine> {
  // machine, final state, num steps, macro size used
  let mut rem_todo = vec![];
  let mut results: Vec<(SmallBinMachine, State, u32, usize)> = vec![];
  for machine in machines {
    // println!("working on machine {}", machine.to_compact_format());
    let mut rulebook = Rulebook::chain_rulebook(&machine);
    let (new_state, steps) = simulate_proving_rules(&machine, num_steps, &mut rulebook, false);
    if new_state == State::INFINITE && verbose {
      println!("\n{}", machine.to_compact_format());
      simulate_proving_rules(
        &machine,
        num_steps,
        &mut Rulebook::chain_rulebook(&machine),
        true,
      );
    }
    if new_state == State::INFINITE || new_state == HALT {
      results.push((machine, new_state, steps, 1));
    } else {
      rem_todo.push(machine);
    }

    //   let macro_machine: MacroMachine<State, Bit, 2> = MacroMachine::new(machine.clone());
    //   let mut rulebook = Rulebook::chain_rulebook(&macro_machine);
    //   let (new_state, steps) =
    //     simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, false);
    //   if new_state == MacroState::INFINITE || new_state.halted() {
    //     results.push((machine, new_state.get_state(), steps, 2));
    //   } else {
    //     let macro_machine: MacroMachine<State, Bit, 3> = MacroMachine::new(machine.clone());
    //     let mut rulebook = Rulebook::chain_rulebook(&macro_machine);
    //     let (new_state, steps) =
    //       simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, false);

    //     results.push((machine, new_state.get_state(), steps, 3));
    //   }
  }
  let rem_todo = prove_macro_size::<2>(rem_todo, num_steps, &mut results, verbose);
  println!("macro size 2 done");
  let rem_todo = prove_macro_size::<3>(rem_todo, num_steps, &mut results, verbose);
  println!("macro size 3 done");
  let rem_todo = prove_macro_size::<4>(rem_todo, num_steps, &mut results, verbose);
  println!("macro size 4 done");
  // let rem_todo = prove_macro_size::<5>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 5 done");
  // let rem_todo = prove_macro_size::<6>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 6 done");
  // let rem_todo = prove_macro_size::<7>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 7 done");
  // let rem_todo = prove_macro_size::<8>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 8 done");
  // let rem_todo = prove_macro_size::<9>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 9 done");
  // let rem_todo = prove_macro_size::<10>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 10 done");
  for m in rem_todo.iter() {
    results.push((m.clone(), State::START, 0, 0));
  }
  aggregate_and_display_macro_proving_res::<10>(&results);
  rem_todo
}

fn get_which_proven(machines: &Vec<SmallBinMachine>, num_steps: u32, verbose: bool) -> Vec<usize> {
  let mut out = vec![];
  for (i, machine) in machines.iter().enumerate() {
    // println!("working on machine {}", machine.to_compact_format());
    let mut rulebook = Rulebook::chain_rulebook(machine);
    let (new_state, _steps) = simulate_proving_rules(machine, num_steps, &mut rulebook, verbose);
    if new_state == State::INFINITE {
      out.push(i);
    }
  }
  out
}

fn list_which_proven(machines: &Vec<SmallBinMachine>, num_steps: u32, verbose: bool) {
  let which_proven = get_which_proven(machines, num_steps, verbose);
  println!("num: {} proven: {:?}", which_proven.len(), &which_proven);
  let proven_set: HashSet<_> = which_proven.into_iter().collect();
  for (i, machine) in machines.iter().enumerate() {
    println!(
      "{} {} m: {} ",
      i,
      proven_set.contains(&i),
      machine.to_compact_format()
    );
  }
}

fn scan_from_machine(
  machine: &SmallBinMachine,
  num_lr_steps: u32,
  num_rule_steps: u32,
  mb_undecided_file: Option<&str>,
) {
  let lr_results = search_for_translated_cyclers(machine, num_lr_steps);
  let undecided_machines = get_undecided(lr_results);
  let undecided_len = undecided_machines.len();
  let undecided_with_halt = undecided_machines
    .into_iter()
    .filter(|m| m.has_halt_trans())
    .collect_vec();
  let remaining_undecided_len = undecided_with_halt.len();
  let no_halt_trans_count = undecided_len - remaining_undecided_len;
  println!(
    "there were {} undecided machines, after determinization.",
    undecided_len
  );
  println!(
    "{} had no halt trans, leaving {} to be decided",
    no_halt_trans_count, remaining_undecided_len,
  );
  let final_undecided = prove_with_macros(undecided_with_halt, num_rule_steps, false);
  if let Some(filename) = mb_undecided_file {
    dump_machines_to_file(final_undecided.clone(), filename).expect("file should be openable");
  }
  let num_undecided_to_display = 10;
  let seed = 123456789012345;
  let mut rng: ChaCha8Rng = SeedableRng::seed_from_u64(seed);
  let random_undecideds = final_undecided
    .choose_multiple(&mut rng, num_undecided_to_display)
    .cloned()
    .collect_vec();

  println!(
    "some undecided machines:\n{}",
    machines_to_str(random_undecideds)
  );
  // println!(
  //   "final_undecided:\n{}",
  //   final_undecided
  //     .iter()
  //     .map(|m| m.to_compact_format())
  //     .join("\n")
  // );
  // let previous_set: HashSet<_> = undecided_size_3()
  //   .into_iter()
  //   .map(|s| SmallBinMachine::from_compact_format(s))
  //   .collect();
  // let final_undecided_new = final_undecided
  //   .iter()
  //   .filter(|m| !previous_set.contains(m))
  //   .collect_vec();
  // println!(
  //   "new_undecided:\n{}",
  //   final_undecided_new
  //     .iter()
  //     .map(|m| m.to_compact_format())
  //     .join("\n")
  // );

  // loop {
  //   println!("Enter the index of a machine you would like to run:");
  //   let mut input_text = String::new();
  //   io::stdin()
  //     .read_line(&mut input_text)
  //     .expect("failed to read from stdin");

  //   let trimmed = input_text.trim();
  //   let i = match trimmed.parse::<usize>() {
  //     Ok(i) => i,
  //     Err(..) => {
  //       println!("this was not an integer: {}", trimmed);
  //       exit(1)
  //     }
  //   };
  //   let machine = &final_undecided[i];
  //   println!("selected machine: {}", machine.to_compact_format());
  //   run_machine(machine);
  // }
}

fn main() {
  // let first_machine = SmallBinMachine::start_machine(4, Bit(true));
  // let num_lr_steps = 1500;
  // let num_rule_steps = 200;
  // scan_from_machine(
  //   &first_machine,
  //   num_lr_steps,
  //   num_rule_steps,
  //   // Some("size3_holdouts_2_may.txt"),
  //   // Some("size4_holdouts_31_may_29e2280.txt"),
  //   None,
  // );

  //give up 5jun23
  // run_machine(&SmallBinMachine::from_compact_format(
  //   "1RB0RB_1LC1RB_1RD1LC_1RH1RA",
  // ));

  // run_machine(&get_machine("4state_halter"));
  // let decideable_by_macro = decideable_by_macro();
  // run_machine_macro::<2>(&SmallBinMachine::from_compact_format(
  //   decideable_by_macro[2],
  // ));
  let bouncers = bouncers();
  for i in 0..10 {
    let machine = SmallBinMachine::from_compact_format(bouncers[i]);
    disp_records(&machine);
  }
}

/*
2 may 23 rule step to machine counts
7820 @ 42-1000
7819 @ 38-41
7818 @ 35-37
7817 @ 34
7816 @ 31-33
7814 @ 30
7810 @ 29
7807 @ 28
7798 @ 27
7789 @ 26
7772 @ 25
7725 @ 24
so the record holding machines take
42
38
35
34
2 @ 31
4 @ 30
3 @ 29
9 @ 28
9 @ 27
27 @ 26
47 @ 25
 */
