#![allow(dead_code)]
#![allow(unused_imports)]
#![feature(return_position_impl_trait_in_trait)]
use std::{io, process::exit};

use crate::{
  linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult},
  rules::{simulate_proving_rules, AffineVar},
  simulate::Tape,
  turing::HALT,
};
use either::Either::Right;
use itertools::Itertools;
use rules::{
  aggregate_and_display_proving_res, detect_chain_rules, simulate_using_rules, Rulebook,
};
use simulate::{tnf_simulate, ExpTape};
use turing::{get_machine, Bit, SmallBinMachine, Turing, INFINITE};

mod linrecur;
mod rules;
mod simulate;
mod turing;
/*
high level todo:
- detect rules that are more than additive (mx + b?)
- rules which consume part of end are probably broken (should maybe emit ConsumedEnd)
- prove rules by induction
- detect counter rules
- macro machines, or tape compression
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


 */

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
  let num_steps = 200;
  Tape::simulate_from_start(machine, num_steps, true);
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  println!("using rules");
  simulate_using_rules::<Bit, u32>(machine, num_steps, &rulebook, true);
  println!("\n\nproving rules");
  simulate_proving_rules(machine, num_steps, &mut rulebook, true);
}

fn get_undecided(res: Vec<(SmallBinMachine, LRResult)>) -> Vec<SmallBinMachine> {
  res
    .into_iter()
    .filter_map(|(m, r)| match r {
      LRResult::Inconclusive { steps_simulated: _ } => Some(m),
      _ => None,
    })
    .flat_map(|m| m.determinize_machine())
    .collect_vec()
}

fn prove_with_rules(
  machines: Vec<SmallBinMachine>,
  num_steps: u32,
  verbose: bool,
) -> Vec<SmallBinMachine> {
  let mut results = vec![];
  for machine in machines {
    let mut rulebook = Rulebook::chain_rulebook(&machine);
    let (new_state, steps) = simulate_proving_rules(&machine, num_steps, &mut rulebook, false);
    if new_state == INFINITE && verbose {
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
      if s != INFINITE && s != HALT {
        Some(m)
      } else {
        None
      }
    })
    .collect_vec()
}
fn undecided_size_3() -> Vec<&'static str> {
  vec![
    "1RB1RH_1RC0LC_1LB0RB",
    "1RB1RH_1RC1LB_0LB0RC",
    "1RB1LA_1RC1RB_1LA1RH",
    "1RB0RB_1LC1RH_0LA1RC",
    "1RB1RA_1LC1RH_1RA1LC",
    "1RB1RA_1LC1RH_0RA1LC",
    "1RB1RH_1LC1RB_0RB0LC",
    "1RB1RH_1LC1RB_0RA0LC",
    "1RB1RH_1LC1RA_0RA0LC",
    "1RB1RH_1LC0RB_0LC1RB",
    "1RB1RH_1LC0RC_1RB0LB",
    "1RB1RH_1LC0RA_1RB0LB",
    "1RB1RH_1LC0RA_0RB0LB",
    "1RB1RC_1LC1RH_0RA0LB",
    "1RB1LA_1LC0LC_1RH1RA",
    "1RB1LC_1LC1RB_1RH1LA",
    "1RB0LB_1LC1RB_1RH1LA",
    "1RB1RH_1LC0RB_1LB1LA",
    "1RB1RC_0RC1RH_1LC0LA",
    "1RB0RC_0RC1RH_1LC0LA",
    "1RB1RH_0RC0LB_1LB1RC",
    "1RB1RH_0RC1LB_1LA0LA",
    "1RB1RH_0LC0RB_1RB1LC",
    "1RB1RH_0LC1RB_1LA1LC",
    "1RB1RA_0LC1RH_0RA1LC",
    "1RB1RH_0LC0RA_1LA1LB",
    "1RB1RH_0LC0RB_0RA1LB",
    "1RB1RH_0LC0RA_0RA1LB",
    "1RB0LC_0LC1RA_1RH1LA",
    "1RB0LC_1LB1RA_1RH1LA",
    "1RB1RH_0LB1RC_1LB0RC",
    "1RB0RC_1LA1RB_1RH1LB",
    "1RB0LC_1LA0RA_1LA1RH",
    "1RB0LB_1LA0RC_1RB1RH",
    "1RB1LA_1LA1RC_1RH1RB",
    "1RB1LA_1LA0LC_1RH1RA",
    "1RB1LC_0LA0RB_1LA1RH",
    "1RB0LC_0LA0RA_1LA1RH",
    "1RB1LA_0LA0LC_1RH1RA",
  ]
}
// running machine: 1RB1LA_0LA0LC_1RH1RA

fn scan_3_dregs() {
  for m_str in undecided_size_3() {
    let machine = SmallBinMachine::from_compact_format(m_str);
    run_machine(&machine);
  }
}

fn scan_3_size_2() {
  let two_state_no_halt_from_scan_3 = vec![
    /*
    A FF FF< (TF, n) FF
    A FF< (TF, n+2)
     */
    "1RB0LB_1LA0RA",
    /*
    phase: B  (F, 1) (T, 1 + 1*x_0) |>F<| (F, 1)
    into:
    phase: B  (T, 3 + 1*x_0) |>F<|
     */
    "1RB1LA_1LA1RB",
    /*
    phase: A  (F, 1) |>F<| (T, 1 + 1*x_0) (F, 1)
    into:
    phase: A   |>F<| (T, 2 + 1*x_0) (F, 1)
     */
    "1RB1LA_0LA1RB",
    // binary counter, count grows leftwards
    "1RB1LA_0LA0RB",
  ];
  for m_str in two_state_no_halt_from_scan_3 {
    let machine = SmallBinMachine::from_compact_format(m_str);
    run_machine(&machine);
  }
}

fn scan_from_machine(machine: &SmallBinMachine, num_steps: u32) {
  let lr_results = search_for_translated_cyclers(machine, num_steps);
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
  let final_undecided = prove_with_rules(undecided_with_halt, 200, false);
  println!(
    "final_undecided:\n{}",
    final_undecided
      .iter()
      .map(|m| m.to_compact_format())
      .join("\n")
  );

  loop {
    println!("Enter the index of a machine you would like to run:");
    let mut input_text = String::new();
    io::stdin()
      .read_line(&mut input_text)
      .expect("failed to read from stdin");

    let trimmed = input_text.trim();
    let i = match trimmed.parse::<usize>() {
      Ok(i) => i,
      Err(..) => {
        println!("this was not an integer: {}", trimmed);
        exit(1)
      }
    };
    let machine = &final_undecided[i];
    println!("selected machine: {}", machine.to_compact_format());
    run_machine(machine);
  }
}
fn main() {
  // let first_machine = SmallBinMachine::start_machine(3, Bit(true));
  // let num_steps = 500;
  // scan_from_machine(&first_machine, num_steps);

  // let machine = get_machine("tailEatingDragonFast");
  let machine = SmallBinMachine::from_compact_format("1RB1LA_0LA0LC_1RH1RA");
  let lr_res = lr_simulate(&machine, 50);
  println!("{:?}", lr_res);
  run_machine(&machine);

  // scan_3_dregs();
}
