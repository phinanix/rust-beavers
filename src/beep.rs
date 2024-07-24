
use std::{collections::HashSet, fs};

use either::Either::{Left, Right};
use itertools::Itertools;
use rand::prelude::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::{
  brady::{difference_of, find_records, get_rs_hist_for_machine, split_and_filter_records, Record},
  linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult},
  macro_machines::{MacroMachine, MacroState},
  rules::{detect_chain_rules, Rulebook},
  simulate::{aggregate_and_display_macro_proving_res, aggregate_and_display_proving_res, simulate_proving_rules},
  tape::{disp_list_bit,tnf_simulate, ExpTape, Tape},
  turing::{Bit, Dir, Phase, SmallBinMachine, State, TapeSymbol, Turing, HALT},
  turing_examples::{bouncers, decideable_by_macro, get_machine, undecided_size_4_random_100},
};

// by convention, the first step at which a state is never used again is the 
// QH state. eg if a machine never uses a state, it quasihalts at step 0
// if a machine only uses state A at the very start and then immediately 
// transitions to B, it quasihalts at step 1
pub enum LRResultBeep {
  QHHalt { qh_step: u32, halt_step: u32},
  QHCycle { qh_step: u32, start_step: u32, period: u32 },
  NonQHCycle { start_step: u32, period: u32 },
  QHLR { qh_step: u32, start_step: u32, period: u32 },
  NonQHLR { start_step: u32, period: u32 },
  Inconclusive { steps_simulated: u32 },
}
use LRResultBeep::*;
  
struct LastUsed {num_states: u8, step: u32, last_used: [i32; 10]}

impl LastUsed {
  pub fn new(num_states: u8) -> Self {
    LastUsed { num_states, step: 0, last_used: [-1; 10] }
  }

  pub fn state_used(&mut self, state: u8, cur_step: u32) {
    assert_eq!(self.step, cur_step);
    self.last_used[state as usize] = cur_step.try_into().unwrap();
  }

  fn state_slice(&self) -> &[i32] {
    &self.last_used[1..=(self.num_states as usize)]
  }

  pub fn qh_time(&self) -> u32 {
    assert!(self.num_states < 10 && self.num_states > 0, "bad many states {}", self.num_states);
    let ans = self.state_slice().iter().max().unwrap() + 1;
    ans.try_into().unwrap()
  }

  pub fn all_used_after(&self, step: u32) -> bool {
    self.state_slice().iter().all(|&step_used| {
      let su : u32 = step_used.try_into().unwrap();
      assert_ne!(su, step); 
      su > step
    })
  }
}

fn detect_quasihalt_of_halter(machine: &SmallBinMachine, halt_steps: u32) -> u32 {
  let mut tape: Tape<Bit> = Tape::new();
  let mut state = State::START;
  let mut steps_taken = 0;

  let mut last_used = LastUsed::new(machine.num_states());
  last_used.state_used(State::START.as_byte(), steps_taken);

  while steps_taken <= halt_steps {
    state = match tape.step_dir(state, machine) {
      Left(_unknown_edge) => unreachable!("machine is defined"),
      Right((new_state, _mb_dir, steps)) => {
        steps_taken += steps;
        last_used.state_used(new_state.as_byte(), steps_taken);

        if new_state.halted() {
          assert_eq!(steps_taken, halt_steps);
          return last_used.qh_time()
        }

        new_state
      }
    };
  }

  panic!("halt detected first time but not second time {}", machine.to_compact_format())
}

/* 
  here's a simpler algorithm for deciding whether a machine quasihalts by LR / Cycle: 
    1. decide whether LR/Cycle exists
    2. now knowing the length of LR/Cycle, step through the machine starting 
        at 0 and length, and track the last time each transition was used 
        in the slow and fast track
    3. once LR/Cycle is detected, you must decide whether the repeating block
        uses all transitions. you can do this by comparing the last_used_fast
        to the time at which cycling starts. if all transitions are used in the
        repeating block, that is a proof of non-quasi-halt
    4. otherwise, the machine quasihalts before it enters the repeating block. 
        to determine when, use the last_used_slow data structure
*/
/*
repeat_steps is the number of steps slow and fast were apart when the recurrence
  was detected
repeat_by_steps is the number of steps slow had taken when the recurrence was 
  detected
*/
fn detect_quasihalt_of_lr_or_cycler(
  machine: &SmallBinMachine, repeat_steps: u32, repeat_by_steps: u32
) -> LRResultBeep {

  let to_print = false;
  let mut fast_tape: Tape<Bit> = Tape::new();
  let mut fast_state = State::START;
  let mut fast_steps = 0;
  let mut fast_cur_displacement = 0;
  let mut fast_last_used = LastUsed::new(machine.num_states());
  fast_last_used.state_used(State::START.as_byte(), 0);

  for _fast_step in 0..repeat_steps {
    fast_state = match fast_tape.step_dir(fast_state, machine) {
      Left(_unknown_edge) => unreachable!("machine is defined"),
      Right((new_state, mb_dir, steps)) => {
        assert_eq!(steps, 1);
        fast_steps += steps;
        if new_state.halted() {
          unreachable!("nonhalter halted fast {}", machine.to_compact_format());
        }
        fast_last_used.state_used(new_state.as_byte(), fast_steps);
        //unwrap justified because we didn't halt
        fast_cur_displacement += mb_dir.unwrap().to_displacement();
        // leftmost = leftmost.min(cur_displacement);
        // rightmost = rightmost.max(cur_displacement);
        new_state
      }
    };

  }

  let mut slow_tape: Tape<Bit> = Tape::new();
  let mut slow_state = State::START;
  let mut slow_steps = 0;
  let mut slow_cur_displacement = 0;
  let mut slow_last_used = LastUsed::new(machine.num_states());
  slow_last_used.state_used(State::START.as_byte(), 0);
  
  // let mut num_at_which_we_check = 0;
  // let mut next_power_of_two = 1;
  // let mut tape_to_check = tape.clone();
  // let mut state_to_check = state.clone();
  // let mut displacement_to_check = cur_displacement;

  // let mut leftmost = todo!();
  // let mut rightmost = todo!();

  for _slow_step in 0..repeat_by_steps {
  
    // if to_print {
    //   println!("steps: {} state: {:?} tape: {}", steps_taken, state, &tape);
    // }

    // cycle check
    if fast_state == slow_state && fast_tape == slow_tape {
      let start_step = slow_steps;
      let period = repeat_steps;
      if fast_last_used.all_used_after(start_step) {
        // all were used, so no qh
        return NonQHCycle { start_step, period }
      } else {
        // one was not used, so we qh immediately before entering this cycle
        let qh_time = slow_last_used.qh_time();
        return QHCycle { qh_step: qh_time, start_step, period }
      }
    }
  
    // LR check
    /* list of conditions:
    - states match
    - tape matches within (l, r)
    - (l, r) \subset (l+shift, r+shift) union dead tape
    */
    if fast_state == slow_state {
      let shift = fast_cur_displacement - slow_cur_displacement;
      // todo: we need to calculate left 
      let leftmost: i32 = 0;
      let rightmost: i32 = 0;
      // todo: this is duplicating some work with all the indexing stuff
      let start_left: i32 = leftmost
        .abs_diff(slow_cur_displacement)
        .try_into()
        .unwrap();
      let start_right: i32 = rightmost
        .abs_diff(slow_cur_displacement)
        .try_into()
        .unwrap();

      let end_left: i32 = (leftmost + shift)
        .abs_diff(fast_cur_displacement)
        .try_into()
        .unwrap();
      let end_right: i32 = (rightmost + shift)
        .abs_diff(fast_cur_displacement)
        .try_into()
        .unwrap();
      let index_left: i32 = (fast_tape.left_length() as i32).min(end_left);
      let index_right: i32 = (fast_tape.right_length() as i32).min(end_right);
      if to_print {
        dbg!(
          shift,
          fast_cur_displacement,
          slow_cur_displacement,
          leftmost,
          rightmost
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
      if index_left <= start_left + shift && index_right <= start_right - shift {
        let start_tape_slice =
          slow_tape.get_displaced_slice(leftmost, rightmost, slow_cur_displacement);
        let cur_tape_slice =
          fast_tape.get_displaced_slice(leftmost + shift, rightmost + shift, fast_cur_displacement);
        if to_print {
          // dbg!(start_tape_slice, cur_tape_slice);
          println!("fast_tape: {} slow_tape: {}", fast_tape, slow_tape);
        }
        if start_tape_slice == cur_tape_slice {
          let start_step = slow_steps;
          let period = repeat_steps;
          if fast_last_used.all_used_after(start_step) {
            // all were used, so no qh
            return NonQHLR { start_step, period }
          } else {
            // one was not used, so we qh immediately before entering this cycle
            let qh_time = slow_last_used.qh_time();
            return QHLR { qh_step: qh_time, start_step, period }
          }
        }
      }
      if to_print {
        println!()
      }
    }
  
    // update power of two
    // if steps_taken == next_power_of_two {
    //   num_at_which_we_check = next_power_of_two;
    //   next_power_of_two *= 2;
    //   tape_to_check = tape.clone();
    //   state_to_check = state.clone();
    //   displacement_to_check = cur_displacement;
    //   leftmost = cur_displacement;
    //   rightmost = cur_displacement;
    // }

    // update slow stuff
    slow_state = match slow_tape.step_dir(slow_state, machine) {
      Left(_unknown_edge) => unreachable!("machine is defined"),
      Right((new_state, mb_dir, steps)) => {
        assert_eq!(steps, 1);
        slow_steps += steps;
        if new_state.halted() {
          unreachable!("nonhalter halted slow {}", machine.to_compact_format());
        }
        slow_last_used.state_used(new_state.as_byte(), slow_steps);
        //unwrap justified because we didn't halt
        slow_cur_displacement += mb_dir.unwrap().to_displacement();
        // leftmost = leftmost.min(cur_displacement);
        // rightmost = rightmost.max(cur_displacement);
        new_state
      }
    };
    
    // update fast stuff
    fast_state = match fast_tape.step_dir(fast_state, machine) {
      Left(_unknown_edge) => unreachable!("machine is defined"),
      Right((new_state, mb_dir, steps)) => {
        assert_eq!(steps, 1);
        fast_steps += steps;
        if new_state.halted() {
          unreachable!("nonhalter halted fast {}", machine.to_compact_format());
        }
        fast_last_used.state_used(new_state.as_byte(), fast_steps);
        //unwrap justified because we didn't halt
        fast_cur_displacement += mb_dir.unwrap().to_displacement();
        // leftmost = leftmost.min(cur_displacement);
        // rightmost = rightmost.max(cur_displacement);
        new_state
      }
    };

  }

  todo!()
}

pub fn lr_simulate_beep<P: Phase, S: TapeSymbol>(
  machine: &impl Turing<P, S>, num_steps: u32
) -> LRResultBeep
  where Tape<S>: std::fmt::Display,
{
  let to_print = false;
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
  while steps_taken < num_steps {
    state = match tape.step_dir(state, machine) {
      Left(_unknown_edge) => unreachable!("machine is defined"),
      Right((new_state, mb_dir, steps)) => {
        steps_taken += steps;
        if new_state.halted() {
          todo!();
          // return Halt { num_steps: steps_taken };
        }
        //unwrap justified because we didn't halt
        cur_displacement += mb_dir.unwrap().to_displacement();
        leftmost = leftmost.min(cur_displacement);
        rightmost = rightmost.max(cur_displacement);
        new_state
      }
    };
  
    if to_print {
      println!("steps: {} state: {:?} tape: {}", steps_taken, state, &tape);
    }
    // cycle check
    if state == state_to_check && tape == tape_to_check {
      let start_step = num_at_which_we_check;
      todo!();
      // return Cycle {
      //   start_step,
      //   period: steps_taken - num_at_which_we_check,
      // };
    }
  
    // LR check
    /* list of conditions:
    - states match
    - tape matches within (l, r)
    - (l, r) \subset [(l+shift, r+shift) union dead tape]
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
      let index_left: i32 = (tape.left_length() as i32).min(end_left);
      let index_right: i32 = (tape.right_length() as i32).min(end_right);
      if to_print {
        dbg!(
          shift,
          cur_displacement,
          displacement_to_check,
          leftmost,
          rightmost
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
      if index_left <= start_left + shift && index_right <= start_right - shift {
        let start_tape_slice =
          tape_to_check.get_displaced_slice(leftmost, rightmost, displacement_to_check);
        let cur_tape_slice =
          tape.get_displaced_slice(leftmost + shift, rightmost + shift, cur_displacement);
        if to_print {
          // dbg!(start_tape_slice, cur_tape_slice);
          println!("tape: {} tape_to_check: {}", tape, tape_to_check);
        }
        if start_tape_slice == cur_tape_slice {
          todo!();
          // return LR {
          //   start_step: steps_taken,
          //   period: steps_taken - num_at_which_we_check,
          // };
        }
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
  

pub fn search_for_translated_cyclers_beep(
    first_machine: &SmallBinMachine,
    num_steps: u32,
  ) -> Vec<(SmallBinMachine, LRResult)> {
    let machines = tnf_simulate(first_machine.clone(), 130, true);
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
  
pub fn scan_from_machine_beep(
    machine: &SmallBinMachine,
    num_lr_steps: u32,
    num_rule_steps: u32,
    mb_undecided_file: Option<&str>,
) {
let lr_results = search_for_translated_cyclers_beep(machine, num_lr_steps);
// let undecided_machines = get_undecided(lr_results);
// let undecided_len = undecided_machines.len();
// let undecided_with_halt = undecided_machines
//     .into_iter()
//     .filter(|m| m.has_halt_trans())
//     .collect_vec();
// let remaining_undecided_len = undecided_with_halt.len();
// let no_halt_trans_count = undecided_len - remaining_undecided_len;
// println!(
//     "there were {} undecided machines, after determinization.",
//     undecided_len
// );
// println!(
//     "{} had no halt trans, leaving {} to be decided",
//     no_halt_trans_count, remaining_undecided_len,
// );
// let final_undecided = prove_with_macros(undecided_with_halt, num_rule_steps, false);
// if let Some(filename) = mb_undecided_file {
//     dump_machines_to_file(final_undecided.clone(), filename).expect("file should be openable");
// }
// let num_undecided_to_display = 10;
// let seed = 123456789012345;
// let mut rng: ChaCha8Rng = SeedableRng::seed_from_u64(seed);
// let random_undecideds = final_undecided
//     .choose_multiple(&mut rng, num_undecided_to_display)
//     .cloned()
//     .collect_vec();

// println!(
//     "some undecided machines:\n{}",
//     machines_to_str(random_undecideds)
// );
// println!(
//   "final_undecided:\n{}",
//   final_undecided
//     .iter()
//     .map(|m| m.to_compact_format())
//     .join("\n")
// );
// let previous_set: HashSet<_> = undecided_size_3()
//   .into_iter()
//   .map(|s| SmallBinMachine::from_compact_format(s))
//   .collect();
// let final_undecided_new = final_undecided
//   .iter()
//   .filter(|m| !previous_set.contains(m))
//   .collect_vec();
// println!(
//   "new_undecided:\n{}",
//   final_undecided_new
//     .iter()
//     .map(|m| m.to_compact_format())
//     .join("\n")
// );

// loop {
//   println!("Enter the index of a machine you would like to run:");
//   let mut input_text = String::new();
//   io::stdin()
//     .read_line(&mut input_text)
//     .expect("failed to read from stdin");

//   let trimmed = input_text.trim();
//   let i = match trimmed.parse::<usize>() {
//     Ok(i) => i,
//     Err(..) => {
//       println!("this was not an integer: {}", trimmed);
//       exit(1)
//     }
//   };
//   let machine = &final_undecided[i];
//   println!("selected machine: {}", machine.to_compact_format());
//   run_machine(machine);
// }
}
