#![allow(dead_code)]
#![allow(unused_imports)]
#![feature(int_roundings)]
// #![feature(return_position_impl_trait_in_trait)]



use std::fmt::Display;
use std::{collections::HashSet, fs, io};

use beep::{detect_quasihalt_of_lr_or_cycler, scan_from_filename_beep};
use brady::{monotonic, print_mb_proof, split_records, try_prove_bouncer, BouncerProof, MbBounce};
use either::Either::{Left, Right};
use itertools::Itertools;
use rand::{prelude::SliceRandom, Rng};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::{
  beep::{search_for_translated_cyclers_beep, scan_from_machine_beep},
  brady::{difference_of, split_and_filter_records, Record, find_records, get_rs_hist_for_machine},
  linrecur::{aggregate_and_display_lr_res, lr_simulate, LRResult},
  macro_machines::{MacroMachine, MacroState},
  rules::{detect_chain_rules, Rulebook},
  simulate::{aggregate_and_display_macro_proving_res, aggregate_and_display_proving_res, simulate_proving_rules},
  tape::{disp_list_bit,tnf_simulate, ExpTape, Tape},
  turing::{Bit, SmallBinMachine, Turing, Dir, Phase, State, HALT},
  turing_examples::{bouncers, decideable_by_macro, undecided_size_4_random_100, get_machine},
};


mod beep;
mod brady;
mod chain;
mod linrecur;
mod macro_machines;
mod parse;
mod rules;
mod simulate;
mod tape;
mod turing;
mod turing_examples;

/*
to prove tail eating dragon:
- detect rules that are more than additive (mx + b?)

high level todo:
- when you guess a rule, assert that it is conserving
- chain rules which decrease by 2 or more
- rules which consume part of end are probably broken (should maybe emit ConsumedEnd)
- prove rules by induction
- detect counter rules
- chain rules which deal with modular conditions
- macro machines, or tape compression
- detect rules by repeats of transitions/rules used, rather than by tape repeating
- implicit end of tape -> explicit (?)
- track step count of rules
- heuristics based on tape growth
- bit packed tape?
- parallelize bb5 search?
*/

/* lower level todo 21 Apr 23
1) test rule prover works on any other machine
2) test rule prover works on a machine that needs a "second level" rule (a rule to prove a rule)
3) detect when a rule runs forever (using iterate_rule)
4) mb fix proving same rule more than once
5) scan tm3 and tm4 (mb tm5)
6) counters / rule induction
7) fixed size macro machines
 */

/*
rule proving status: it "mostly" "works"
current issues that need fixing:
1) it tries to prove the same rule over and over, which is obviously a big waste of time
2) relatedly, it doesn't know when a rule means it can run forever, so we need to detect that

musings on rules (1 may 23)
some rules are "necessary", most obviously anything made by chaining - in that we can't necessarily prove anything without using them
other rules are not, so maybe we just drop them?
 */

/*
todo 21 aug 23
* record records and history as we simulate
* implement heuristics based on records
* implement bouncer detector
* implement counter detector
 */

#[derive(Debug)]
struct BL<'a>(&'a [Bit]);

impl<'a> Display for BL<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&disp_list_bit(&self.0))
    }
}

fn machines_to_str(machines: Vec<SmallBinMachine>) -> String {
  machines
    .into_iter()
    .map(|m| m.to_compact_format())
    .join("\n")
}

fn machines_to_idx_str(machines: Vec<SmallBinMachine>) -> String {
  machines
    .into_iter().enumerate()
    .map(|(idx, m)| format!("{} {}", idx, m.to_compact_format()))
    .join("\n")
}

fn strs_to_machine(m_strs: Vec<&str>) -> Vec<SmallBinMachine> {
  m_strs
    .into_iter()
    .map(|m_str| SmallBinMachine::from_compact_format(m_str))
    .collect_vec()
}

fn dump_machines_to_file(machines: Vec<SmallBinMachine>, filename: &str) -> std::io::Result<()> {
  let machine_len = machines.len();
  let big_str = machines_to_str(machines);
  fs::write(filename, big_str)?;
  println!("wrote {} machines to file: {}", machine_len, filename);
  Ok(())
}

fn load_machines_from_file(filename: &str) -> Vec<SmallBinMachine> {
  let message = match fs::read_to_string(filename) {
    Ok(message) => message,
    Err(err) => panic!("tried to read file {} but got {}", filename, err),
  };
  message.lines().map(|m_str| SmallBinMachine::from_compact_format(m_str)).collect_vec()  
}

fn search_for_translated_cyclers(
  first_machine: &SmallBinMachine,
  num_steps: u32,
) -> Vec<(SmallBinMachine, LRResult)> {
  // note that 130 is plenty here
  let machines = tnf_simulate(first_machine.clone(), 140, false);
  // dbg!(machines.len());
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
  lr_results
}

fn run_machine(machine: &SmallBinMachine) {
  println!("\nrunning machine: {}", machine.to_compact_format());
  // let chain_rules = detect_chain_rules(machine);
  // println!("{} chain rules:", chain_rules.len());
  // for (i, chain_rule) in chain_rules.iter().enumerate() {
    // println!("{}: {}", i, chain_rule);
  // }
  // println!();

  // let mut rulebook = Rulebook::new(machine.num_states());
  // rulebook.add_rules(chain_rules);
  let num_steps = 100;
  Tape::simulate_from_start(machine, num_steps * 3, true);
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  // println!("using rules");
  // simulate_using_rules::<Bit, u32>(machine, num_steps, &rulebook, true);
  // println!("\n\nproving rules");
  // simulate_proving_rules(machine, num_steps, &mut rulebook, true);
}

fn run_machine_interactive(machine: &SmallBinMachine) {
  println!("\nrunning machine: {}", machine.to_compact_format());
  let mut input_text = String::new();
    io::stdin()
    .read_line(&mut input_text)
    .expect("failed to read from stdin");
  // let chain_rules = detect_chain_rules(machine);
  // println!("{} chain rules:", chain_rules.len());
  // for (i, chain_rule) in chain_rules.iter().enumerate() {
    // println!("{}: {}", i, chain_rule);
  // }
  // println!();

  // let mut rulebook = Rulebook::new(machine.num_states());
  // rulebook.add_rules(chain_rules);
  let num_steps = 200;
  Tape::simulate_from_start(machine, num_steps * 3, true);
  let ans = try_prove_bouncer(machine); 
  println!("mb proof: {}", print_mb_proof(&ans));
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  // println!("using rules");
  // simulate_using_rules::<Bit, u32>(machine, num_steps, &rulebook, true);
  // println!("\n\nproving rules");
  // simulate_proving_rules(machine, num_steps, &mut rulebook, true);
}

fn run_machine_macro<const N: usize>(machine: &SmallBinMachine) {
  println!(
    "\nrunning machine: {}\nat macro size: {}",
    machine.to_compact_format(),
    N
  );
  let macro_machine: MacroMachine<_, _, N> = MacroMachine::new(machine.clone());
  let chain_rules = detect_chain_rules(&macro_machine);
  println!("{} chain rules:", chain_rules.len());
  for (i, chain_rule) in chain_rules.iter().enumerate() {
    println!("{}: {}", i, chain_rule);
  }
  println!();

  let mut rulebook = Rulebook::new(macro_machine.num_states());
  rulebook.add_rules(chain_rules);
  let num_steps = 30;
  Tape::simulate_from_start(machine, num_steps, true);
  // println!("vanilla");
  // ExpTape::simulate_from_start(machine, num_steps);
  // println!("using rules");
  // simulate_using_rules::<Bit, u32>(machine, num_steps, &rulebook, true);
  println!("\n\nproving rules");
  simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, true);
}

fn get_undecided(res: Vec<(SmallBinMachine, LRResult)>) -> Vec<SmallBinMachine> {
  let verbose = true;
  res
    .into_iter()
    .filter_map(|(m, r)| match r {
      LRResult::Inconclusive { steps_simulated: _ } => Some(m),
      _ => None,
    })
    .flat_map(|m| {
      let ans = m.determinize_machine();
      if verbose && !(ans.len() == 1 || ans.len() == 32) {
        println!(
          "{} -> {} {:?}",
          m.to_compact_format(),
          ans.len(),
          ans.iter().map(|m| m.to_compact_format()).collect_vec()
        )
      }
      ans
    })
    .collect_vec()
}

fn prove_with_rules(
  machines: Vec<SmallBinMachine>,
  num_steps: u32,
  verbose: bool,
) -> Vec<SmallBinMachine> {
  let mut results = vec![];
  for machine in machines {
    // println!("working on machine {}", machine.to_compact_format());
    let mut rulebook = Rulebook::chain_rulebook(&machine);
    let (new_state, steps) = simulate_proving_rules(&machine, num_steps, &mut rulebook, false);
    if new_state == State::INFINITE && verbose {
      println!("\n{}", machine.to_compact_format());
      simulate_proving_rules(
        &machine,
        num_steps,
        &mut Rulebook::chain_rulebook(&machine),
        true,
      );
    }
    results.push((machine, new_state, steps));
  }
  aggregate_and_display_proving_res(&results);
  results
    .into_iter()
    .filter_map(|(m, s, _steps)| {
      if s != State::INFINITE && s != HALT {
        Some(m)
      } else {
        None
      }
    })
    .collect_vec()
}

fn prove_macro_size<const N: usize>(
  machines: Vec<SmallBinMachine>,
  num_steps: u32,
  results: &mut Vec<(SmallBinMachine, State, u32, usize)>,
  _verbose: bool,
) -> Vec<SmallBinMachine> {
  let mut out = vec![];
  for machine in machines {
    let macro_machine: MacroMachine<State, Bit, N> = MacroMachine::new(machine.clone());
    let mut rulebook = Rulebook::chain_rulebook(&macro_machine);
    let (new_state, steps) =
      simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, false);
    if new_state == MacroState::INFINITE || new_state.halted() {
      results.push((machine, new_state.get_state(), steps, N));
    } else {
      out.push(machine);
    }
  }
  out
}

fn prove_with_macros(
  machines: Vec<SmallBinMachine>,
  num_steps: u32,
  verbose: bool,
) -> Vec<SmallBinMachine> {
  // machine, final state, num steps, macro size used
  let mut rem_todo = vec![];
  let mut results: Vec<(SmallBinMachine, State, u32, usize)> = vec![];
  for machine in machines {
    // println!("working on machine {}", machine.to_compact_format());
    let mut rulebook = Rulebook::chain_rulebook(&machine);
    let (new_state, steps) = simulate_proving_rules(&machine, num_steps, &mut rulebook, false);
    if new_state == State::INFINITE && verbose {
      println!("\n{}", machine.to_compact_format());
      simulate_proving_rules(
        &machine,
        num_steps,
        &mut Rulebook::chain_rulebook(&machine),
        true,
      );
    }
    if new_state == State::INFINITE || new_state == HALT {
      results.push((machine, new_state, steps, 1));
    } else {
      rem_todo.push(machine);
    }

    //   let macro_machine: MacroMachine<State, Bit, 2> = MacroMachine::new(machine.clone());
    //   let mut rulebook = Rulebook::chain_rulebook(&macro_machine);
    //   let (new_state, steps) =
    //     simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, false);
    //   if new_state == MacroState::INFINITE || new_state.halted() {
    //     results.push((machine, new_state.get_state(), steps, 2));
    //   } else {
    //     let macro_machine: MacroMachine<State, Bit, 3> = MacroMachine::new(machine.clone());
    //     let mut rulebook = Rulebook::chain_rulebook(&macro_machine);
    //     let (new_state, steps) =
    //       simulate_proving_rules(&macro_machine, num_steps, &mut rulebook, false);

    //     results.push((machine, new_state.get_state(), steps, 3));
    //   }
  }
  let rem_todo = prove_macro_size::<2>(rem_todo, num_steps, &mut results, verbose);
  println!("macro size 2 done");
  let rem_todo = prove_macro_size::<3>(rem_todo, num_steps, &mut results, verbose);
  println!("macro size 3 done");
  let rem_todo = prove_macro_size::<4>(rem_todo, num_steps, &mut results, verbose);
  println!("macro size 4 done");
  // let rem_todo = prove_macro_size::<5>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 5 done");
  // let rem_todo = prove_macro_size::<6>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 6 done");
  // let rem_todo = prove_macro_size::<7>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 7 done");
  // let rem_todo = prove_macro_size::<8>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 8 done");
  // let rem_todo = prove_macro_size::<9>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 9 done");
  // let rem_todo = prove_macro_size::<10>(rem_todo, num_steps, &mut results, verbose);
  // println!("macro size 10 done");
  for m in rem_todo.iter() {
    results.push((m.clone(), State::START, 0, 0));
  }
  aggregate_and_display_macro_proving_res::<10>(&results);
  rem_todo
}

fn get_which_proven(machines: &Vec<SmallBinMachine>, num_steps: u32, verbose: bool) -> Vec<usize> {
  let mut out = vec![];
  for (i, machine) in machines.iter().enumerate() {
    // println!("working on machine {}", machine.to_compact_format());
    let mut rulebook = Rulebook::chain_rulebook(machine);
    let (new_state, _steps) = simulate_proving_rules(machine, num_steps, &mut rulebook, verbose);
    if new_state == State::INFINITE {
      out.push(i);
    }
  }
  out
}

fn list_which_proven(machines: &Vec<SmallBinMachine>, num_steps: u32, verbose: bool) {
  let which_proven = get_which_proven(machines, num_steps, verbose);
  println!("num: {} proven: {:?}", which_proven.len(), &which_proven);
  let proven_set: HashSet<_> = which_proven.into_iter().collect();
  for (i, machine) in machines.iter().enumerate() {
    println!(
      "{} {} m: {} ",
      i,
      proven_set.contains(&i),
      machine.to_compact_format()
    );
  }
}

fn prove_with_brady_bouncer(machines: Vec<SmallBinMachine>) -> Vec<(SmallBinMachine, MbBounce)> {
  let mut out = vec![];
  for (_i, machine) in machines.into_iter().enumerate() {
    // dbg!(i);
    let proof_res = try_prove_bouncer(&machine);
    out.push((machine, proof_res))

  }
  out
}

fn scan_from_machines(
  machines: &[SmallBinMachine],
  num_lr_steps: u32,
  _num_rule_steps: u32,
  mb_undecided_file: Option<&str>,
) {
  let mut lr_results = vec![];
  for machine in machines { 
    lr_results.extend(search_for_translated_cyclers(machine, num_lr_steps));
  }
  aggregate_and_display_lr_res(lr_results.iter().map(|(_m, res)| *res).collect());

  let undecided_machines = get_undecided(lr_results);
  let undecided_len = undecided_machines.len();
  let undecided_with_halt = undecided_machines
    .into_iter()
    .filter(|m| m.has_halt_trans())
    .collect_vec();
  let remaining_undecided_len = undecided_with_halt.len();
  let no_halt_trans_count = undecided_len - remaining_undecided_len;
  println!(
    "there were {} undecided machines, after determinization.",
    undecided_len
  );
  println!(
    "{} had no halt trans, leaving {} to be decided",
    no_halt_trans_count, remaining_undecided_len,
  );
  let bouncer_results = prove_with_brady_bouncer(undecided_with_halt);
  let bouncer_proofs = bouncer_results.iter().map(|(_, p)| p.clone()).collect_vec();
  aggregate_and_display_bouncer_res(&bouncer_proofs);
  let final_undecided = get_bouncer_undecided(bouncer_results);
  // let final_undecided = prove_with_macros(undecided_with_halt, num_rule_steps, false);
  
  if let Some(filename) = mb_undecided_file {
    dump_machines_to_file(final_undecided.clone(), filename).expect("file should be openable");
  }
  
  // let num_undecided_to_display = 10;
  // let seed = 123456789012345;
  // let mut rng: ChaCha8Rng = SeedableRng::seed_from_u64(seed);
  // let random_undecideds = final_undecided
  //   .choose_multiple(&mut rng, num_undecided_to_display)
  //   .cloned()
  //   .collect_vec();

  // println!(
    //   "some undecided machines:\n{}",
  //   machines_to_str(random_undecideds)
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

fn get_bouncer_undecided(bouncer_results: Vec<(SmallBinMachine, Result<BouncerProof, &str>)>) 
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


fn scan_from_machine(
  machine: &SmallBinMachine,
  num_lr_steps: u32,
  num_rule_steps: u32,
  mb_undecided_file: Option<&str>,
) {
  scan_from_machines(&vec![machine.clone()][..], num_lr_steps, num_rule_steps, mb_undecided_file);
}

fn scan_from_filename(
  filename: &str, 
  num_lr_steps: u32,
  num_rule_steps: u32,
  mb_undecided_file: Option<&str>,
) {
  let machines = load_machines_from_file(filename);
  scan_from_machines(&machines, num_lr_steps, num_rule_steps, mb_undecided_file);
}

fn run_random_machines_from_file(
  filename: &str, 
  num_machines: usize, 
) {
  let machines = load_machines_from_file(filename);
  let seed = 123456789012345;
  let mut rng: ChaCha8Rng = SeedableRng::seed_from_u64(seed);
  let mut random_machines = vec![];
  for _ in 0..num_machines {
    let idx = rng.gen_range(0..machines.len());
    random_machines.push(machines[idx].clone());
  }
  // let random_machines = machines
  //   .choose_multiple(&mut rng, num_machines)
  //   .cloned()
  //   .collect_vec();

  println!("all machines:\n{}\n\n{}", machines_to_str(random_machines.clone()), machines_to_idx_str(random_machines.clone()));
  for (idx, machine) in random_machines.iter().enumerate() {
    println!("\nidx {}", idx);
    run_machine_interactive(&machine)
  }
}

fn aggregate_and_display_bouncer_res(proofs: &[Result<BouncerProof, &str>]) {
  let mut bounce_proof_count = 0;
  let mut undecided_count = 0; 
  for proof in proofs {
    match proof {
      Err(_s) => undecided_count+=1, 
      Ok(_p) => bounce_proof_count+=1, 
    }
  }
  assert_eq!(bounce_proof_count + undecided_count, proofs.len());
  println!(
    "analyzed {} machines. bouncers: {} undecided: {}", 
    proofs.len(), bounce_proof_count, undecided_count
  )
}

fn main() {
  // 1_000 instead of 1_000_000 misses 296 machines (of ~3M, so 0.01%), but we can always come back to those
  let num_lr_steps = 1_000;
  let num_rule_steps = 200;
  dbg!(num_lr_steps, num_rule_steps);

  let first_machine = SmallBinMachine::start_machine(4, Bit(true));
  // scan_from_machine(
  scan_from_machine_beep(
    &first_machine,
    num_lr_steps,
    num_rule_steps,
    // Some("size3_holdouts_2_may.txt"),
    // Some("size4_holdouts_31_may_29e2280.txt"),
    // Some("size4_bouncer_not_quite_qh_holdouts_2_august_24"),
    None,
  );

  // scan_from_filename_beep(
  //   "size4_qh_holdouts_24_july_24", 
  //   num_lr_steps, 
  //   num_rule_steps, 
  //   None,
  // );

  // run_random_machines_from_file(
  //   "size4_bouncer_not_quite_qh_holdouts_2_august_24",
  //   // "size3_qh_holdouts_30_july_24",
  //   25);

  // let m = SmallBinMachine::from_compact_format("1RB---_1RC---_1RD1LD_1LD1RC");
  // run_machine(&m);
  // detect_quasihalt_of_lr_or_cycler(&m, 2, 4);

  //LR "not defined" crash 24jul24
  // run_machine(&SmallBinMachine::from_compact_format("1RB1LC_1RC0LA_1RD0RE_1RE---_1LE1LB"));
  // run_machine(&SmallBinMachine::from_compact_format("1RB0LD_1RC0RB_1RD0LA_1RE1LA_1LD---"));

  //give up 5jun23
  // run_machine(&SmallBinMachine::from_compact_format(
  //   "1RB0RB_1LC1RB_1RD1LC_1RH1RA",
  // ));

  // run_machine(&get_machine("4state_halter"));
  // let decideable_by_macro = decideable_by_macro();
  // run_machine_macro::<2>(&SmallBinMachine::from_compact_format(
  //   decideable_by_macro[2],
  // ));

  // let mut proofs = vec![];
  // let random_undecided = undecided_size_4_random_100();
  // // let bouncers = bouncers();
  // let machines = random_undecided;
  // for i in 0..machines.len() {
  //   let machine = SmallBinMachine::from_compact_format(machines[i]);
  //   println!("{}: {}", i, machine.to_compact_format());
  //   let proof_res = try_prove_bouncer(&machine);
  //   println!("{}\n\n", print_mb_proof(&proof_res));
  //   proofs.push(proof_res);
  // }
  // println!("proofs");
  // for (i, mb_proof) in proofs.iter().enumerate() {
  //   println!("{}: {}", i, print_mb_proof(mb_proof));
  // }
  // aggregate_and_display_bouncer_res(&proofs);
}

/*
2 may 23 rule step to machine counts
7820 @ 42-1000
7819 @ 38-41
7818 @ 35-37
7817 @ 34
7816 @ 31-33
7814 @ 30
7810 @ 29
7807 @ 28
7798 @ 27
7789 @ 26
7772 @ 25
7725 @ 24
so the record holding machines take
42
38
35
34
2 @ 31
4 @ 30
3 @ 29
9 @ 28
9 @ 27
27 @ 26
47 @ 25
 */
