#![allow(dead_code)]
#![allow(unused_imports)]
use crate::{
  linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult},
  rules::{simulate_proving_rules, AffineVar},
  simulate::Tape,
  turing::HALT,
};
use either::Either::Right;
use itertools::Itertools;
use rules::{detect_chain_rules, simulate_detect_rules, simulate_using_rules, Rulebook};
use simulate::{tnf_simulate, ExpTape};
use turing::{get_machine, Bit, SmallBinMachine, Turing};

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

fn search_for_translated_cyclers(first_machine: SmallBinMachine, num_steps: u32) {
  let machines = tnf_simulate(first_machine, 130);
  dbg!(machines.len());
  let mut lr_results = vec![];
  for m in machines {
    let m_str = SmallBinMachine::to_compact_format(&m);
    let lr_res = lr_simulate(&m, num_steps);
    lr_results.push(lr_res);
    let (final_state, normal_num_steps, _tape) = Tape::simulate_from_start(&m, num_steps, false);

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
  aggregate_and_display_lr_res(lr_results);
}

fn main() {
  // let first_machine = SmallBinMachine::start_machine(4, Bit(true));
  // let num_steps = 1300;
  // search_for_translated_cyclers(first_machine, num_steps);
  let machine = get_machine("sweeper");
  let chain_rules = detect_chain_rules(&machine);
  println!("{} chain rules:", chain_rules.len());
  for (i, chain_rule) in chain_rules.iter().enumerate() {
    println!("{}: {}", i, chain_rule);
  }
  println!();

  let mut rulebook = Rulebook::new(machine.num_states());
  rulebook.add_rules(chain_rules);
  let num_steps = 10;
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  println!("using rules");
  simulate_using_rules::<Bit, u32>(&machine, num_steps, &rulebook, false);
  // println!("detecting rules");
  // simulate_detect_rules(machine, num_steps, &rulebook, false);
  println!("proving rules");
  simulate_proving_rules(&machine, num_steps, &mut rulebook, true);
}
