use either::Either::{Left, Right};
use crate::{
  simulate::{Tape, TapeSymbol},
  turing::{Turing, START},
};

#[allow(unused)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LRResult {
  Halt { num_steps: u32 },
  Cycle { start_step: u32, period: u32 },
  LR { start_step: u32, period: u32 },
  Inconclusive { steps_simulated: u32 },
}
use LRResult::*;

pub fn lr_simulate<S: TapeSymbol>(machine: &impl Turing<S>, num_steps: u32) -> LRResult {
  let mut tape: Tape<S> = Tape::new();
  let mut state = START;
  let mut cur_displacement = 0;
  let mut steps_taken = 0;

  let mut num_at_which_we_check = 0;
  let mut next_power_of_two = 1; 
  let mut tape_to_check = tape.clone();
  let mut state_to_check = state.clone();
  let mut displacement_to_check = cur_displacement;
  let mut leftmost = cur_displacement; 
  let mut rightmost = cur_displacement;
  while steps_taken < num_steps {
    state = match tape.step_dir(state, machine) {
        Left(_unknown_edge) => unreachable!("machine is defined"),
        Right((new_state, dir)) => {
          cur_displacement += dir.to_displacement();
          leftmost = leftmost.min(cur_displacement);
          rightmost = rightmost.max(cur_displacement);
          new_state
        },
    };
    steps_taken += 1;

    // cycle check 
    if state == state_to_check && tape == tape_to_check {
      let start_step = num_at_which_we_check;
      return Cycle { start_step, period: steps_taken - num_at_which_we_check }
    }

    // LR check 
    /* list of conditions: 
    - states match
    - tape matches within (l, r)
    - (l, r) \subset (l+shift, r+shift) union dead tape
    */ 
    if state == state_to_check {
      let start_tape_slice = tape_to_check.get_displaced_slice(leftmost, rightmost, displacement_to_check);
      let cur_tape_slice = tape.get_displaced_slice(leftmost, rightmost, cur_displacement);
      if start_tape_slice == cur_tape_slice {

      }
    }

    // update power of two
    if steps_taken == next_power_of_two {
      num_at_which_we_check = next_power_of_two; 
      next_power_of_two *= 2; 
      tape_to_check = tape.clone();
      state_to_check = state.clone();
      displacement_to_check = cur_displacement;
      leftmost = cur_displacement;
      rightmost = cur_displacement;
    }
  }
  Inconclusive { steps_simulated: num_steps }
}

mod test {
  use super::*;
  use crate::turing::{get_machine, HALT};

  #[test] 
  fn index_oob(){
    let myvec = vec![0, 1, 2, 3];
    dbg!(&myvec[1..6]);
  }
}