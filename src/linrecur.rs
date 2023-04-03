use either::Either::{Left, Right};
use crate::{
  simulate::{Tape, TapeSymbol},
  turing::{Turing, START, HALT},
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

pub fn lr_simulate<S: TapeSymbol>(machine: &impl Turing<S>, num_steps: u32) -> LRResult
 where Tape<S> : std::fmt::Display {
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
        Right((HALT, _dir)) => return Halt{num_steps: steps_taken+1},
        Right((new_state, dir)) => {
          cur_displacement += dir.to_displacement();
          leftmost = leftmost.min(cur_displacement);
          rightmost = rightmost.max(cur_displacement);
          new_state
        },
    };
    steps_taken += 1;
    // println!("steps: {} state: {:?} tape: {}", steps_taken, state, &tape);

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
      let shift = cur_displacement - displacement_to_check;
      // todo: this is duplicating some work with all the indexing stuff
      let start_left = leftmost.abs_diff(displacement_to_check).try_into().unwrap();
      let start_right = rightmost.abs_diff(displacement_to_check).try_into().unwrap();
      let end_left = (leftmost + shift).abs_diff(cur_displacement).try_into().unwrap();
      let end_right = (rightmost + shift).abs_diff(cur_displacement).try_into().unwrap();
      let index_left = tape.left_length().min(end_left);
      let index_right = tape.right_length().min(end_right);
      // dbg!(shift, cur_displacement, displacement_to_check, leftmost, rightmost);
      // dbg!(start_left, start_right, end_left, end_right, index_left, index_right);
      // println!();
      if index_left <= start_left && index_right <= start_right {
        let start_tape_slice = tape_to_check.get_displaced_slice(leftmost, rightmost, displacement_to_check);
        let cur_tape_slice = tape.get_displaced_slice(leftmost+shift, rightmost+shift, cur_displacement);
        // dbg!(start_tape_slice, cur_tape_slice);
        if start_tape_slice == cur_tape_slice {
          return LR { start_step: steps_taken, period: steps_taken - num_at_which_we_check }
        }
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
  use crate::turing::{get_machine, HALT, SmallBinMachine};

  #[test]
  fn lr_finds_simple_machine() {
    let m_str = "1RB---_1RB---";
    let m = SmallBinMachine::from_compact_format(m_str);
    let lr_res = lr_simulate(&m, 5);
    assert_eq!(lr_res, LR { start_step: 2, period: 1 });
  }
}