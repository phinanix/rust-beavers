use crate::turing::Turing;

#[allow(unused)]

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LRResult {
  Halt{num_steps: u32},
  LR{start_step: u32, period: u32}, 
  Inconclusive{steps_simulated: u32}
}

pub fn lr_simulate<S>(machine: &impl Turing<S>, num_steps: u32) -> LRResult {
  todo!()
} 