
use std::{collections::HashSet, fs, io, process::exit};

use either::Either::{Left, Right};
use itertools::Itertools;
use rand::prelude::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::{
  aggregate_and_display_bouncer_res, brady::{construct_bouncer_proof, difference_of, find_bouncer_wxyz, find_records, get_rs_hist_for_machine, split_and_filter_records, try_prove_bouncer, BouncerProof, MbBounce, Record}, dump_machines_to_file, get_bouncer_undecided, linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult}, load_machines_from_file, machines_to_str, macro_machines::{MacroMachine, MacroState}, prove_with_brady_bouncer, rules::{detect_chain_rules, Rulebook}, run_machine, simulate::{aggregate_and_display_macro_proving_res, aggregate_and_display_proving_res, simulate_proving_rules}, tape::{disp_list_bit,tnf_simulate, ExpTape, Tape}, turing::{Bit, Dir, Phase, SmallBinMachine, State, TapeSymbol, Turing, HALT}, turing_examples::{bouncers, decideable_by_macro, get_machine, undecided_size_4_random_100}
};

// by convention, the first step at which a state is never used again is the 
// QH state. eg if a machine never uses a state, it quasihalts at step 0
// if a machine only uses state A at the very start and then immediately 
// transitions to B, it quasihalts at step 1
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    assert!(num_states < 10 && num_states > 0, "bad many states {}", num_states);
    LastUsed { num_states, step: 0, last_used: [-1; 10] }
  }

  pub fn state_used(&mut self, state: u8, cur_step: u32) {
    assert_eq!(self.step, cur_step);
    self.last_used[state as usize] = cur_step.try_into().unwrap();
    self.step += 1;
  }

  fn state_slice(&self) -> &[i32] {
    &self.last_used[1..=(self.num_states as usize)]
  }

  pub fn qh_time(&self) -> u32 {
    let ans = self.state_slice().iter().max().unwrap() + 1;
    ans.try_into().unwrap()
  }

  pub fn all_used_after(&self, step: u32) -> bool {
    self.state_slice().iter().all(|&step_used| {
      // dbg!(step_used);
      let compare_step : i32 = step.try_into().unwrap();
      assert_ne!(step_used, compare_step); 
      step_used > compare_step
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
pub fn detect_quasihalt_of_lr_or_cycler(
  machine: &SmallBinMachine, repeat_steps: u32, repeat_by_steps: u32
) -> LRResultBeep {

  let to_print = false;
  let mut fast_tape: Tape<Bit> = Tape::new();
  let mut fast_state = State::START;
  let mut fast_steps = 0;
  let mut fast_cur_displacement = 0;
  let mut fast_disp_history = vec![fast_cur_displacement];
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
        fast_disp_history.push(fast_cur_displacement);        
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

  for _slow_step in 0..=repeat_by_steps {
  
    if to_print {
      println!("slow steps: {} state: {:?} tape: {}", slow_steps, slow_state, &slow_tape);
      println!("fast steps: {} state: {:?} tape: {}", fast_steps, fast_state, &fast_tape);
    }

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
      // todo: we need to calculate leftmost and rightmost
      let disp_hist_slice = &fast_disp_history[(slow_steps as usize)..=(fast_steps as usize)];
      let leftmost: i32 = *disp_hist_slice.iter().min().unwrap();
      let rightmost: i32 = *disp_hist_slice.iter().max().unwrap();


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

      let l_len = fast_tape.left_length() as i32;
      let r_len = fast_tape.right_length() as i32;

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
        if shift > 0 {
          assert!(r_len == (rightmost - fast_cur_displacement));
          // assert!(r_len <= (rightmost - displacement_to_check));
        } else if shift < 0 {
          assert!(l_len == -1 * (leftmost - fast_cur_displacement));
        }

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
        fast_disp_history.push(fast_cur_displacement);        
        // leftmost = leftmost.min(cur_displacement);
        // rightmost = rightmost.max(cur_displacement);
        new_state
      }
    };

  }

  panic!("we should have detected an lr or a cycle but we didn't {} {:?} {} {}", 
      machine.to_compact_format(), lr_simulate(machine, 1500), repeat_steps, repeat_by_steps)
}

pub fn lr_simulate_beep(
  machine: &SmallBinMachine, num_steps: u32
) -> LRResultBeep
{
  let lr_res = lr_simulate(machine, num_steps);
  let (start_step, period) = match lr_res {
    LRResult::Inconclusive { steps_simulated } => return Inconclusive { steps_simulated },
    LRResult::Halt { num_steps } => {
      let qh_time = detect_quasihalt_of_halter(machine, num_steps);
      return QHHalt { qh_step: qh_time, halt_step: num_steps }
    },
    LRResult::Cycle { start_step, period } => (start_step, period),
    LRResult::LR { start_step, period } => (start_step, period),
  };
  detect_quasihalt_of_lr_or_cycler(machine, period, start_step)
  
}
  
pub fn aggregate_and_display_lr_res_beep(results: Vec<LRResultBeep>) {
  let total_machines = results.len();

  let mut halt_count = 0;
  let mut qh_cycle_count = 0;
  let mut nqh_cycle_count = 0;
  let mut qh_lr_count = 0;
  let mut nqh_lr_count = 0;
  let mut inconclusive_count = 0;
  for result in results {
    match result {
      QHHalt { .. } => halt_count += 1,
      QHCycle { .. } => qh_cycle_count += 1,
      NonQHCycle { .. } => nqh_cycle_count += 1,
      QHLR { .. } => qh_lr_count += 1,
      NonQHLR { .. } => nqh_lr_count += 1,
      Inconclusive { steps_simulated: _steps_simulated } => inconclusive_count += 1,
    }
  }
  println!(
    "total machines: {}\nhalted: {} quasihalted (cycled): {} quashalted (lr): {}\nnon-qh (cycled): {} non-qh (lr): {} inconclusive: {}",
    total_machines,
    halt_count, qh_cycle_count, qh_lr_count,
    nqh_cycle_count, nqh_lr_count, inconclusive_count
  );
}

pub fn search_for_translated_cyclers_beep(
    first_machine: &SmallBinMachine,
    num_steps: u32,
  ) -> Vec<(SmallBinMachine, LRResultBeep)> {
    let machines = tnf_simulate(first_machine.clone(), 130, true);
    // dbg!(machines.len());
    let mut lr_results = vec![];
    for m in machines {
      // let m_str = SmallBinMachine::to_compact_format(&m);
      let lr_res = lr_simulate_beep(&m, num_steps);
      lr_results.push((m, lr_res));
    }
    // aggregate_and_display_lr_res_beep(lr_results.iter().map(|(_m, res)| *res).collect());
    lr_results
}

fn get_undecided_beep(res: Vec<(SmallBinMachine, LRResultBeep)>) -> Vec<SmallBinMachine> {
  // let verbose = true;
  res
    .into_iter()
    .filter_map(|(m, r)| match r {
      LRResultBeep::Inconclusive { steps_simulated: _ } => Some(m),
      _ => None,
    })
    .collect_vec()
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum BouncerQHProof {
  BouncerQH{proof: BouncerProof, qh_time: u32},
  BouncerNonQH{proof: BouncerProof}
}
use BouncerQHProof::*;

type MbQHBounce = Result<BouncerQHProof, &'static str>;

fn get_last_used_to_time(machine: &SmallBinMachine, steps_to_simulate: u32) -> LastUsed {
  let mut tape: Tape<Bit> = Tape::new();
  let mut state = State::START;
  // let mut steps = 0;
  let mut last_used = LastUsed::new(machine.num_states());
  last_used.state_used(state.as_byte(), 0);
  for step in 1..=steps_to_simulate {
    state = match tape.step_dir(state, machine) {
      Left(_unknown_edge) => unreachable!("machine is defined"),
      Right((new_state, _mb_dir, steps)) => {
        assert_eq!(steps, 1);
        if new_state.halted() {
          unreachable!("nonhalter halted fast lastused {}", machine.to_compact_format());
        }
        last_used.state_used(new_state.as_byte(), step);
        new_state
      }
    }
  }
  last_used
}

fn decide_qh_via_bouncer(
  machine: &SmallBinMachine, num_wxyz_steps: u32, max_proof_steps: u32, max_proof_tape: usize, print: bool,
) ->  MbQHBounce {
  // let print = true;
  // let (w, x, y, z, state_0) = find_bouncer_wxyz(&machine, num_wxyz_steps, print)?;
  // let (proof, state_set) = construct_bouncer_proof(
  //   &machine, state_0, &w, &x, &y, &z, 
  //   max_proof_steps, max_proof_tape, print)?;
  let (proof, state_set) = try_prove_bouncer(machine, num_wxyz_steps, max_proof_steps, max_proof_tape, print)?;
  /* in order to figure out whether the bouncer qh'd we need two things 
   1) which states are used in the bouncing itself
   2) the last_used up to the point at which the bouncer starts bouncing, which 
      at the latest happens at num_wxyz_steps, so we can use that as an upper bound
  */
  if state_set.len() == machine.num_states().into() {
    // machine does not QH, as all states are used during bouncing
    return Ok(BouncerNonQH { proof })
  }
  assert!(state_set.len() < machine.num_states().into(), 
      "more states used than available {}", machine.to_compact_format());
      
  // machine qhs at some point before starting bouncing, we just need to find when
  let last_used = get_last_used_to_time(machine, num_wxyz_steps);
  // todo add some sort of assert / sanity check that the machine does actually use the specified 
  // states near the end of the checked part and no more or less
  let qh_time = last_used.qh_time();
  Ok(BouncerQH { proof, qh_time })
}

fn prove_qh_with_brady_bouncer(machines: Vec<SmallBinMachine>) 
  -> Vec<(SmallBinMachine, MbQHBounce)> 
{
  let print = false;
  
  let num_wxyz_steps = 10_000;
  let max_proof_steps = 20_000;
  let max_proof_tape = 300;
  // let num_wxyz_steps = 3_000;
  // let max_proof_steps = 1_000;
  // let max_proof_tape = 100;
  println!("wxyz steps: {} proof steps: {} proof max_tape: {}", 
  num_wxyz_steps, max_proof_steps, max_proof_tape); 
  
  let mut out = vec![];

  for (_i, machine) in machines.into_iter().enumerate() {
    // dbg!(i);
    let proof_res = decide_qh_via_bouncer(
      &machine, num_wxyz_steps, max_proof_steps, max_proof_tape, print);
    out.push((machine, proof_res))

  }
  out
}

fn aggregate_and_display_bouncer_res_beep(proofs: &[MbQHBounce]) {
  let mut bounce_qh_proof_count = 0;
  let mut bounce_nqh_proof_count = 0;
  let mut undecided_count = 0; 
  for proof in proofs {
    match proof {
      Err(_s) => undecided_count+=1, 
      Ok(BouncerQH{..}) => bounce_qh_proof_count+=1, 
      Ok(BouncerNonQH{..}) => bounce_nqh_proof_count+=1, 
    }
  }
  assert_eq!(bounce_qh_proof_count + bounce_nqh_proof_count + undecided_count, proofs.len());
  let bounce_proof_count = bounce_qh_proof_count + bounce_nqh_proof_count;
  println!(
    "analyzed {} machines. bouncers: {} of which QH bouncers: {} notQH bouncers: {} undecided: {}", 
    proofs.len(), bounce_proof_count, bounce_qh_proof_count, bounce_nqh_proof_count, undecided_count
  )
}

fn get_bouncer_undecided_beep(bouncer_results: Vec<(SmallBinMachine, MbQHBounce)>) 
  -> Vec<SmallBinMachine> 
{
    let mut out = vec![];
    for res in bouncer_results {
      match res {
          (_m, Ok(_p)) => (),
          (m, Err(_s)) => out.push(m),
      }
    }
    out
}

pub fn scan_from_machines_beep(
    machines: &[SmallBinMachine],
    num_lr_steps: u32,
    _num_rule_steps: u32,
    interactive: bool, 
    mb_undecided_file: Option<&str>,
) {
  let mut lr_results = vec![];
  for machine in machines { 
    lr_results.extend(search_for_translated_cyclers_beep(machine, num_lr_steps));
  }
  aggregate_and_display_lr_res_beep(lr_results.iter().map(|(_m, res)| *res).collect());


  // let lr_results = search_for_translated_cyclers_beep(machine, num_lr_steps);
  let undecided_machines = get_undecided_beep(lr_results);
  let undecided_len = undecided_machines.len();
  println!(
      "there were {} undecided machines",
      undecided_len
  );
  let bouncer_results = prove_qh_with_brady_bouncer(undecided_machines);
  let bouncer_proofs: Vec<Result<BouncerQHProof, &str>> = bouncer_results.iter().map(|(_, p)| p.clone()).collect_vec();
  aggregate_and_display_bouncer_res_beep(&bouncer_proofs);
  let final_undecided = get_bouncer_undecided_beep(bouncer_results);
  


  // let final_undecided = undecided_machines;
  if let Some(filename) = mb_undecided_file {
      dump_machines_to_file(final_undecided.clone(), filename).expect("file should be openable");
  }
  let num_undecided_to_display = 10;
  let seed = 123456789012345;
  let mut rng: ChaCha8Rng = SeedableRng::seed_from_u64(seed);
  let random_undecideds = final_undecided
      .choose_multiple(&mut rng, num_undecided_to_display)
      .cloned()
      .collect_vec();

  println!(
      "some undecided machines:\n{}",
      machines_to_str(random_undecideds)
  );
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

  if interactive {
    loop {
      println!("Enter the index of a machine you would like to run [not of the previous list]:");
      let mut input_text = String::new();
      io::stdin()
        .read_line(&mut input_text)
        .expect("failed to read from stdin");

      let trimmed = input_text.trim();
      let i = match trimmed.parse::<usize>() {
        Ok(i) => i,
        Err(..) => {
          println!("this was not an integer: {}", trimmed);
          exit(1)
        }
      };
      let machine = &final_undecided[i];
      println!("selected machine: {}", machine.to_compact_format());
      run_machine(machine);
    }
  }
}


pub fn scan_from_machine_beep(
  machine: &SmallBinMachine,
  num_lr_steps: u32,
  num_rule_steps: u32,
  interactive: bool, 
  mb_undecided_file: Option<&str>,
) {
  scan_from_machines_beep(&vec![machine.clone()][..], num_lr_steps, num_rule_steps, interactive, mb_undecided_file);
}

pub fn scan_from_filename_beep(
  filename: &str, 
  num_lr_steps: u32,
  num_rule_steps: u32,
  interactive: bool, 
  mb_undecided_file: Option<&str>,
) {
  let machines = load_machines_from_file(filename);
  println!("there were {} machines total in the file {}", machines.len(), filename);
  scan_from_machines_beep(&machines, num_lr_steps, num_rule_steps, interactive, mb_undecided_file);
}
