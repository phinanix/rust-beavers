use crate::{
  tape::Tape,
  turing::{Phase, TapeSymbol, Turing},
};
use either::Either::{Left, Right};

#[allow(unused)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LRResult {
  Halt { num_steps: u32 },
  Cycle { start_step: u32, period: u32 },
  LR { start_step: u32, period: u32 },
  Inconclusive { steps_simulated: u32 },
}
use LRResult::*;

pub fn lr_simulate<P: Phase, S: TapeSymbol>(machine: &impl Turing<P, S>, num_steps: u32) -> LRResult
where
  Tape<S>: std::fmt::Display,
{
  let to_print = false;
  if to_print {
    println!("machine {}", machine.to_compact_format());
  }
  let mut tape: Tape<S> = Tape::new();
  let mut state = P::START;
  let mut cur_displacement = 0;
  let mut steps_taken = 0;

  let mut num_at_which_we_check = 0;
  let mut next_power_of_two = 1;
  let mut tape_to_check = tape.clone();
  let mut state_to_check = state.clone();
  let mut displacement_to_check = cur_displacement;
  let mut leftmost = cur_displacement;
  let mut rightmost = cur_displacement;

  // let mut rlen_hist = vec![tape.right_length()];

  while steps_taken < num_steps {
    state = match tape.step_dir(state, machine) {
      Left(_unknown_edge) => unreachable!("machine is defined {}", machine.to_compact_format()),
      Right((new_state, mb_dir, steps)) => {
        steps_taken += steps;
        if new_state.halted() {
          return Halt { num_steps: steps_taken };
        }
        //unwrap justified because we didn't halt
        cur_displacement += mb_dir.unwrap().to_displacement();
        leftmost = leftmost.min(cur_displacement);
        rightmost = rightmost.max(cur_displacement);
        new_state
      }
    };
    let rlen= tape.right_length();


    if to_print {
      println!("steps: {} state: {:?} tape: {} rlen: {}", steps_taken, state, &tape, rlen);
    }
    
    // assert!(*rlen_hist.last().unwrap() <= rlen, "{:?} {}", rlen_hist, rlen);
    // rlen_hist.push(rlen);

    // cycle check
    if state == state_to_check && tape == tape_to_check {
      let start_step = num_at_which_we_check;
      return Cycle {
        start_step,
        period: steps_taken - num_at_which_we_check,
      };
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
      let start_left: i32 = leftmost.abs_diff(displacement_to_check).try_into().unwrap();
      let start_right: i32 = rightmost
        .abs_diff(displacement_to_check)
        .try_into()
        .unwrap();
      let end_left: i32 = (leftmost + shift)
        .abs_diff(cur_displacement)
        .try_into()
        .unwrap();
      let end_right: i32 = (rightmost + shift)
        .abs_diff(cur_displacement)
        .try_into()
        .unwrap();
      assert_eq!(start_left, end_left);
      assert_eq!(start_right, end_right);
      // println!("hi");
      
      let l_len = tape.left_length() as i32;
      let r_len = tape.right_length() as i32;
      let index_left: i32 = l_len.min(end_left);
      let index_right: i32 = r_len.min(end_right);
      
      if to_print {
        dbg!(
          shift,
          cur_displacement,
          displacement_to_check,
          leftmost,
          rightmost,
          l_len,
          r_len,
          steps_taken, 
          num_at_which_we_check,
        );
        dbg!(
          start_left,
          start_right,
          end_left,
          end_right,
          index_left,
          index_right
        );
      }
      assert!(rightmost >= displacement_to_check);
      assert!(leftmost <= displacement_to_check);

      // assert!(r_len <= (rightmost - cur_displacement) || r_len > (rightmost - displacement_to_check));

      // the short version is we need either r_len == rightmost - curdisp
      // or l_len == leftmost - curdisp
      // because that corresponds to the thing where we have written all the bits we are reading to determine 
      // that the lr rule actually applies
      if index_left <= start_left + shift && index_right <= start_right - shift {
        if shift > 0 {
          assert!(r_len == (rightmost - cur_displacement));
          // assert!(r_len <= (rightmost - displacement_to_check));
        } else if shift < 0 {
          assert!(l_len == -1 * (leftmost - cur_displacement));
        } else {
          // panic!();
        }
        let start_tape_slice =
          tape_to_check.get_displaced_slice(leftmost, rightmost, displacement_to_check);
        let cur_tape_slice =
          tape.get_displaced_slice(leftmost + shift, rightmost + shift, cur_displacement);
        if to_print {
          // dbg!(start_tape_slice, cur_tape_slice);
          println!("tape: {} tape_to_check: {}", tape, tape_to_check);
        }
        if start_tape_slice == cur_tape_slice {
          // if steps_taken - num_at_which_we_check > 3 {panic!("steps {} old steps {} ", steps_taken, num_at_which_we_check)};
          if shift > 0 {
            assert!(r_len == (rightmost - cur_displacement), "{}", machine.to_compact_format());
            if r_len != (rightmost - cur_displacement) {
              // println!("{}", machine.to_compact_format());
            } 
            // assert!(r_len <= (rightmost - displacement_to_check));
          } else if shift < 0 {
            assert!(l_len == -1 * (leftmost - cur_displacement), "{}", machine.to_compact_format());
            if l_len != -1 * (leftmost - cur_displacement) {
              // println!("{}", machine.to_compact_format());
            }
          }
          return LR {
            start_step: num_at_which_we_check,
            period: steps_taken - num_at_which_we_check,
          };
        }
      } else {
        assert!(r_len > (rightmost - cur_displacement) || l_len > -1 * (leftmost - cur_displacement));
        if shift > 0 {
          assert!(r_len > (rightmost - cur_displacement));
        } else if shift < 0 {
          assert!(l_len > -1 * (leftmost - cur_displacement));
        }
        // println!();
        // dbg!(
        //   shift,
        //   cur_displacement,
        //   displacement_to_check,
        //   leftmost,
        //   rightmost,
        //   l_len,
        //   r_len,
        // );
        // dbg!(
        //   start_left,
        //   start_right,
        //   // end_left,
        //   // end_right,
        //   index_left,
        //   index_right
        // );
        // println!("fail");
      }
      if to_print {
        println!()
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

pub fn aggregate_and_display_lr_res(results: Vec<LRResult>) {
  let mut halt_count = 0;
  let mut cycle_count = 0;
  let mut lr_count = 0;
  let mut inconclusive_count = 0;
  for result in results {
    match result {
      Halt { num_steps: _num_steps } => halt_count += 1,
      Cycle { start_step: _start_step, period: _period } => cycle_count += 1,
      LR { start_step: _start_step, period: _period } => lr_count += 1,
      Inconclusive { steps_simulated: _steps_simulated } => inconclusive_count += 1,
    }
  }
  println!(
    "halted: {} cycled: {} lr: {} inconclusive: {}",
    halt_count, cycle_count, lr_count, inconclusive_count
  );
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{turing::SmallBinMachine, turing_examples::get_machine};

  #[test]
  fn lr_finds_simple_machine() {
    let m_str = "1RB---_1RB---";
    let m = SmallBinMachine::from_compact_format(m_str);
    let lr_res = lr_simulate(&m, 5);
    assert_eq!(lr_res, LR { start_step: 2, period: 1 });
  }

  #[test]
  fn lr_not_find_not_lr() {
    let m_strs = ["binary_counter", "checkerboard_sweeper", "sweeper"];
    for m_str in m_strs {
      dbg!(m_str);
      let m = get_machine(m_str);
      let lr_res = lr_simulate(&m, 200);
      assert_eq!(lr_res, Inconclusive { steps_simulated: 200 })
    }
  }
}
