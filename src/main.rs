use simulate::tnf_simulate;
use turing::SmallBinMachine;

mod simulate;
mod turing;
/*
high level todo:
- branch simulation on undefined transition
Get here on 29 Mar is easy-ish goal :)
- driver of the
- detected translated cycling
- rule based simulation
- maybe: make START and HALT states constants
*/
fn main() {
  let first_machine = SmallBinMachine::start_machine(2, true);
  let machines = tnf_simulate(first_machine, 10);
  dbg!(machines.len());
}
