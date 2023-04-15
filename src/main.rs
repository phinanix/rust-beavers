#![allow(dead_code)]
#![allow(unused_imports)]
use crate::{
  linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult},
  simulate::Tape,
  turing::HALT,
};
use either::Either::Right;
use itertools::Itertools;
use rules::simulate_detect_rules;
use simulate::{tnf_simulate, ExpTape};
use turing::{get_machine, Bit, SmallBinMachine};

mod linrecur;
mod rules;
mod simulate;
mod turing;
/*
high level todo:
- rule based simulation
- bit packed tape?
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
  let machine = &get_machine("binary_counter");
  let num_steps = 100;
  ExpTape::simulate_from_start(machine, num_steps);
  simulate_detect_rules(machine, num_steps, false);
}
