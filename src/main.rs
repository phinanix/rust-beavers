#![allow(dead_code)]
#![allow(unused_imports)]
use either::Either::Right;
use itertools::Itertools;
use simulate::tnf_simulate;
use turing::SmallBinMachine;
use crate::{linrecur::{lr_simulate, LRResult}, simulate::Tape, turing::HALT};

mod linrecur;
mod simulate;
mod turing;
/*
high level todo:
- detected translated cycling
- driver of the translated cycler
- rule based simulation
- bit packed tape?
*/
fn main() {
  let first_machine = SmallBinMachine::start_machine(5, true);
  let num_steps = 1300;
  let machines = tnf_simulate(first_machine, num_steps);
  dbg!(machines.len());
  // for m in machines
  // {
  //   let m_str = SmallBinMachine::to_compact_format(&m);
  //   let lr_res = lr_simulate(&m, num_steps);
  //   let (final_state, normal_num_steps, _tape) = Tape::simulate_from_start(&m, num_steps);
    
  //   // println!("m: {}, res: {:?}", m_str, lr_res);
  //   match lr_res {
  //     LRResult::Halt { num_steps: lr_num_steps } => assert_eq!((final_state, normal_num_steps), (Right(HALT), lr_num_steps)),
  //     _ => (),
  //   }
  // }
}
