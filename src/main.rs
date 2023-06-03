#![allow(dead_code)]
#![allow(unused_imports)]
#![feature(return_position_impl_trait_in_trait)]
#![feature(int_roundings)]

use std::{collections::HashSet, fs};

use crate::{
  linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult},
  rules::{detect_chain_rules, Rulebook},
  simulate::{aggregate_and_display_proving_res, simulate_proving_rules},
  tape::Tape,
  turing::{Phase, State},
};
use either::Either::Right;
use itertools::Itertools;
use rand::prelude::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use tape::tnf_simulate;
use turing::{Bit, SmallBinMachine, Turing};

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
- only detect rules when start and end state are same (done)
- detect rules that are more than additive (mx + b?)
- when detecting rules, use ReadShift or similar to not detect extra garbage (like in TailEatingDragonFast)


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
3) biggest issue, it guesses and proves rules that are not "conserving" of tape symbols. there are
   two sub-issues here, essentially.
   a) it guesses rules based on reduced tape signatures (that don't include the infinite ends), but
   the rule (T, x) -> (T, x+1) of course can't hold in a vacuum, it can only hold in the context of
   eating an F from the edge of the tape. ideally we would just prove rules that hold in all
   contexts (this is what readshift is doing in Haskell-bbs but I don't know if that's the easiest
   way to fix this).
   b) when proving a rule, it also freely grabs symbols from the edge of the tape.

   as is, these two issues balance each other out, but it seems perhaps better to fix both of them.
   path to fixing:
   - make Exptape.step return whether you grew/shrunk the tape from the infinite edge (done)
   - make rule application return whether you grew/shrunk the tape (done)
   - in proving, explode if the tape would grow (done)
   - in rule-guessing, track the growing and shrinking such that we can guess a conserving-rule (done)

musings on rules (1 may 23)
some rules are "necessary", most obviously anything made by chaining - in that we can't necessarily prove anything without using them
other rules are not, so maybe we just drop them?
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
        assert_eq!(
          (final_state, normal_num_steps),
          (Right(State::HALT), lr_num_steps)
        )
      }
      _ => (),
    }
    match final_state {
      Right(State::HALT) => assert_eq!(lr_res, LRResult::Halt { num_steps: normal_num_steps }),
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
  let num_steps = 100;
  Tape::simulate_from_start(machine, num_steps, true);
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  // println!("using rules");
  // simulate_using_rules::<Bit, u32>(machine, num_steps, &rulebook, true);
  println!("\n\nproving rules");
  simulate_proving_rules(machine, num_steps, &mut rulebook, true);
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
    println!("working on machine {}", machine.to_compact_format());
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
      if s != State::INFINITE && s != State::HALT {
        Some(m)
      } else {
        None
      }
    })
    .collect_vec()
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
  let final_undecided = prove_with_rules(undecided_with_halt, num_rule_steps, false);
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
  let first_machine = SmallBinMachine::start_machine(4, Bit(true));
  let num_lr_steps = 1500;
  let num_rule_steps = 100;
  scan_from_machine(
    &first_machine,
    num_lr_steps,
    num_rule_steps,
    // Some("size3_holdouts_2_may.txt"),
    // Some("size4_holdouts_31_may_29e2280.txt"),
    None,
  );

  // investigating runs_forever behavior
  // let machine = SmallBinMachine::from_compact_format("1RB1LC_0LA1RH_1RD0LC_1RC1RA");
  // let chain_update = decided_by_chain_update_31may();
  // let machine = SmallBinMachine::from_compact_format(chain_update[0]);
  // run_machine(&machine);

  // let machine = get_machine("tailEatingDragonFast"); // 70 to 73, for example

  // let undecided_size_4_random = strs_to_machine(undecided_size_4_random());
  // let undecided_size_4_random_100 = strs_to_machine(undecided_size_4_random_100());
  // let decrease_rules_make_worse = decrease_rules_make_worse();
  // // 11/30 proven: 0, 1, 2, 4, 6, 9, 14, 15, 19, 20, 29
  // list_which_proven(&undecided_size_4_random, 100, false);
  // // give ups: 18
  // // 7/30 proven: 0, 3, 13, 16, 17, 20, 21,
  // list_which_proven(&undecided_size_4_random_100, 100, false);

  /*
  5  - couldn't chain
  15 - couldn't chain
  22 - couldn't chain
  23 - couldn't chain
  9  - couldn't chain
  19 - couldn't chain
  28 - couldn't chain
   */
  // chainrule fails: 5, 15, 22, 23
  // other fails: 9, 19, 28
  // readshift both ways: 0, 17
  // for i in [5, 15, 22] {
  //   //, 23, 9, 19, 28] {

  // let m_str = decrease_rules_make_worse.get(11).unwrap();
  // let machine = SmallBinMachine::from_compact_format(m_str);
  // let machine = undecided_size_4_random_100.get(18).unwrap();

  // dbg!(machine.to_compact_format());
  // run_machine(&machine);

  // }

  /*
  machines to investigate:
  - the 16 that fail to be proven with >1 decrease
  - what exactly is failing in "failure to guess" eg random_100 at 5,9,15,19,22,23,28
     or random at 11,12,13,18,23
   */

  // scan_3_dregs();
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
