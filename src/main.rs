#![allow(dead_code)]
#![allow(unused_imports)]
use itertools::Itertools;
use simulate::tnf_simulate;
use turing::SmallBinMachine;

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
  let first_machine = SmallBinMachine::start_machine(2, true);
  let machines = tnf_simulate(first_machine, 10);
  dbg!(machines.len());
  for m_str in machines
    .iter()
    .map(|m| SmallBinMachine::to_compact_format(m))
    .collect_vec()
  {
    println!("{}", m_str);
  }
}
