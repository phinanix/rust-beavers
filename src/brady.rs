use std::{fmt::{Debug, Display}, ops::Sub};

use crate::{
  rules::{ReadShift, Rulebook}, simulate::{one_rule_step, RuleStepResult::*}, tape::{disp_list_bit, ExpTape, Tape}, turing::{
    Bit, Dir::{self, L, R}, Phase, SmallBinMachine, State, TapeSymbol, Turing
  }, BL
};
use either::{
  Either,
  Either::{Left, Right},
};
use itertools::Itertools;
use num::CheckedSub;

/*
  returns:
  Left: the step at which the machine was infinite
  or
  Right:
   the tape history, which is a
  Vec<(u32, P, ExpTape<S, u32>)> which is (steps, phase, tape)
  and the Vec<ReadShift>

*/
pub fn get_rs_hist_for_machine<P: Phase, S: TapeSymbol>(
  machine: &impl Turing<P, S>,
  num_steps: u32,
  verbose: bool,
) -> Either<u32, (Vec<(u32, P, ExpTape<S, u32>)>, Vec<ReadShift>)> {
  let rulebook = Rulebook::new(machine.num_states());

  let mut exptape = ExpTape::new(true);
  let mut state = P::START;
  let mut history: Vec<(u32, P, ExpTape<S, u32>)> = vec![];
  let mut readshifts = vec![];

  for step in 1..num_steps + 1 {
    let (new_state, cg_or_rs) =
      match one_rule_step(machine, &mut exptape, state, &rulebook, step, verbose) {
        VarInfinite(_var) => return Left(step),
        RSRInfinite => return Left(step),
        RFellOffTape(_, _) => panic!("fell off tape unexpectedly"),
        RSuccess(state, _hm, cg_or_rs) => (state, cg_or_rs),
      };
    state = new_state;

    let readshift = cg_or_rs.either(|rs| rs, |cg| ReadShift::rs_from_cg(cg));
    if verbose {
      // println!("rs: {:?}", readshift);
    }
    readshifts.push(readshift);

    history.push((step, state, exptape.clone()));

    if state.halted() {
      break;
    }
    // println!("step: {} phase: {} tape: {}", step, state, exptape);
  }
  return Right((history, readshifts));
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Record(pub usize, pub i32, pub Dir);

impl Display for Record {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let Record(step, dist, side) = self;
    write!(f, "Record step: {} dist: {} side: {}", step, dist, side)?;
    Ok(())
  }
}
/*
 parameters: &[ReadShift], the list of readshifts
 returns:   Vec<(usize, i32, Dir)> which is
 (timestamp of record, record distance, record direction)
*/
pub fn find_records(readshifts: &[ReadShift]) -> Vec<Record> {
  let mut cur_rs = ReadShift { l: 0, r: 0, s: 0 };
  let mut out = vec![];
  for (i, &new_rs) in readshifts.into_iter().enumerate() {
    let prev_rs = cur_rs;
    cur_rs = ReadShift::normalize(ReadShift::combine(cur_rs, new_rs));
    if cur_rs.l < prev_rs.l {
      out.push(Record(i, cur_rs.l, Dir::L));
    }
    if cur_rs.r > prev_rs.r {
      out.push(Record(i, cur_rs.r, Dir::R));
    }
  }
  out
}

/*
filters the records such that only first differences in step larger than any seen so far
are kept, which is hopefully the time between tape expansions, rather than during
tape expansions
 */
pub fn filter_records<'a>(mut records: impl Iterator<Item = &'a Record>) -> Vec<Record> {
  let mut out = vec![];
  let mut max_diff_so_far = 0;
  let mut prev_record = match records.next() {
    None => return out, 
    Some(r) => *r,
  };
  for &record in records {
    let diff = record.0.checked_sub(prev_record.0).unwrap();
    if diff > max_diff_so_far {
      max_diff_so_far = diff;
      out.push(record);
    }
    prev_record = record;
  }
  out
}

pub fn split_records(records: Vec<Record>) -> (Vec<Record>, Vec<Record>) {
  let left_records = records.iter().filter(|Record(_, _, d)| *d == L).map(|x| *x).collect_vec();
  let right_records = records.iter().filter(|Record(_, _, d)| *d == R).map(|x| *x).collect_vec();
  (left_records, right_records)
}

/*
returns the left records filtered and the right records filtered
 */
pub fn split_and_filter_records(records: Vec<Record>) -> (Vec<Record>, Vec<Record>) {
  let left_record_iter = records.iter().filter(|Record(_, _, d)| *d == L);
  let right_record_iter = records.iter().filter(|Record(_, _, d)| *d == R);

  let left_records = filter_records(left_record_iter);
  let right_records = filter_records(right_record_iter);
  (left_records, right_records)
}

pub fn monotonic<T: Ord + Copy>(xs: &[T]) -> bool {
  if xs.is_empty() {
    panic!("too short to monotonic")
  }
  let mut prev = xs[0];
  for x in &xs[1..] {
    if *x < prev {
      return false;
    }
    prev = *x;
  }
  return true;
}

pub fn difference_of<T: CheckedSub + Copy + Debug>(xs: &[T]) -> Vec<T> {
  if xs.len() < 2 {
    panic!("too short to take the difference")
  }
  let mut out = vec![];
  let mut last_x = xs[0];
  for x in &xs[1..] {
    out.push((*x).checked_sub(&last_x).unwrap());
    last_x = *x;
  }
  out
}

fn display_record_steps(records: Vec<Record>) {
  if records.len() < 3 {
    println!("records was short: {:?}", records);
    return;
  }
  // for record in records.iter() {
  //   println!("{record}");
  // }
  let steps = records.iter().map(|Record(s, _, _)| *s).collect_vec();
  println!("steps: {:?}", steps);
  if !monotonic(&steps) {
    println!("steps wasn't monotonic");
    return;
  }
  let d1 = difference_of(&steps);
  println!("d1   : {:?}", d1);
  if !monotonic(&d1) {
    println!("d1 wasn't monotonic");
    return;
  }
  let d2 = difference_of(&d1);
  println!("d2   : {:?}", d2);
}

// returns: x, y, z, state, for the config x z^4 y<
pub fn find_bouncer_xyz(machine: &SmallBinMachine) -> Result<(Vec<Bit>, Vec<Bit>, Vec<Bit>, State), &'static str> {
  /*
  goal: extract x, y, z st the machine satisfies x z^n >y => x z^(n+1) >y

  full strat: 
    run machine for N steps, tracking history and readshift
    extract all "records", the times when the tape increases in size
      split those into L and R
      within that, take only times when the difference in stepcount from previous 
       is larger than has been seen so far (since if a machine grows the tape by 2 
       for example, there are 2 records immediately after one another)
    look at the right records, and calculate their "tape extents" 
      (the size of the live tape in each) and the diffs thereof
    if the last 2 diffs are identical, guess that this is a valid size for z, 
      otherwise give up
    assume the last tape is x z^4 y where |x| = |y| (giving the bonus 1 to y
      in the case of an odd number, not that it matters)
    extract x z^4 y
    from z^4 extract z if it is 4 of the same thing, otherwise give up
    return x z y

    the main improvement here to me is that if there is never a right side record, 
    we should switch to using the left side records, but otherwise proceed identically    
   */
  let print = false;
  if print {
    println!(
      "\nrunning records of machine: {}",
      machine.to_compact_format()
    );
  }

  let num_steps = 500;
  if print {
    Tape::simulate_from_start(machine, num_steps, true);
  }

  let (hist, rs) = match get_rs_hist_for_machine(machine, num_steps, false) {
    Left(i) => {
      // no need to block this one, it's very weird
      println!("infinite at {i} steps");
      return Err("machine was infinite");
    }
    Right((hist, rs)) => (hist, rs),
  };
  let records = find_records(&rs);
  if print {
    println!("found {} records", records.len());
  }
  // println!("\nleft");
  // for record in records.iter() {
  //   if record.2 == Dir::L {
  //     println!("{record}");
  //   }
  // }
  // println!("\nright");
  // for record in records.iter() {
  //   if record.2 == Dir::R {
  //     println!("{record}");
  //   }
  // }

  if print {
    let (unfilt_left_records, unfilt_right_records) = split_records(records.clone());
    println!("unfiltered left records");
    display_record_steps(unfilt_left_records.clone());
    println!("unfiltered right records");
    display_record_steps(unfilt_right_records.clone());
  }

  let (left_records, right_records) = split_and_filter_records(records);
  if print {
    println!("\nfiltered left");
    display_record_steps(left_records);
    println!("\nfiltered right");
    display_record_steps(right_records.clone());
  }
  if right_records.len() < 2 {
    return Err("too few right records");
  }
  /* goal: extract |Z| in X Z^n Y
    strategy: look at the filtered right records, take the difference of their tape extents
    hope the last 3 agree
  */
  let mut tape_extents = vec![];
  for Record(r_step, _, _) in right_records.iter() {
    let (step, phase, tape) = &hist[*r_step];
    let tape_extent = tape.len();
    tape_extents.push(tape_extent);
    if print {
      println!(
        "rstep: {} step: {} phase: {} tape: {} tape extent: {} ",
        r_step, step, phase, tape, tape_extent
      );
    }
  }
  if print {
    println!("tape extents: {:?}", tape_extents);
  }

  let tape_diffs = difference_of(&tape_extents);
  if print {
    println!("tape diffs  : {:?}", tape_diffs);
  }
  let mb_len_z = match &tape_diffs[..] {
    [.., d, e, f] => {
      if d == e && e == f {
        Some(*d as usize)
      } else {
        None
      }
    }
    _ => None,
  };
  if print {
    println!("mb len z: {:?}", mb_len_z);
  }
  let len_z: usize = match mb_len_z {
    None => {
      if print {
        println!("couldn't find a len for z");
      }
      return Err("couldn't find a len for z");
    }
    Some(len_z) => len_z,
  };
  assert!(len_z > 0);

  let last_record = right_records.last().unwrap();
  let (_, last_phase, last_tape) = &hist[last_record.0];
  let last_tape_len = last_tape.len() as usize;
  // dbg!(last_tape_len, len_z);
  let rem_last_tape_len = match last_tape_len.checked_sub(4 * len_z) {
    None => return Err("len_z was too big"),
    Some(x) => x,
  };
  let mut len_x = rem_last_tape_len.div_floor(2);
  let mut len_y = rem_last_tape_len.div_ceil(2);
  let last_tape_list: Vec<Bit> = ExpTape::to_tape(last_tape).to_list();
  let z4 = &last_tape_list[len_x..len_x + 4 * len_z];
  assert_eq!(len_x + len_y + 4 * len_z, last_tape_len);
  //include one copy of z so that x is not empty
  if len_x == 0 {len_x += len_z}
  //include one copy of z so that y is not empty
  if len_y == 0 {len_y += len_z}
  let x = &last_tape_list[0..len_x];
  let y = &last_tape_list[(last_tape_list.len() - len_y)..];

  assert_eq!(z4.len(), (len_z * 4) as usize);
  let mut zs = vec![];
  for i in 0..=3 {
    zs.push(&z4[i * len_z..(i + 1) * len_z]);
  }
  let z = match &zs[..] {
    [a, b, c, d] => {
      if a == b && b == c && c == d {
        a
      } else {
        if print {
          println!("failed to extract z from z4: {} and zs: {:?}", BL(z4), zs);
        }
        return Err("failed to extract z from z4 and zs");
      }
    }
    _ => panic!("zs was not length 4"),
  };
  if print {
    println!(
      "extracted x y z from tape at step {}:\n{}\ntapelist:\n{}\nx: {} y: {} z: {}",
      last_record.0,
      last_tape,
      disp_list_bit(&last_tape_list),
      disp_list_bit(x),
      disp_list_bit(y),
      disp_list_bit(z),
    );
  }
  return Ok((x.to_vec(), y.to_vec(), z.to_vec(), *last_phase))

}

fn split_first_n<T>(n: usize, iter: &mut impl Iterator<Item = T>) -> (Vec<T>, Vec<T>) {
  let mut first = vec![];
  let mut second = vec![];
  // let mut count = 0;
  for _i in 0..n {
    first.push(iter.next().unwrap());
  }
  second.extend(iter);
  (first, second)
}

fn split_last_n<T, I : ExactSizeIterator<Item = T>>(
  n: usize, iter: &mut I
) -> (Vec<T>, Vec<T>) 
{  
  assert!(iter.len() > n);
  let first_len = iter.len() - n;
  split_first_n(first_len, iter)
}

pub enum ChunkSimRes {
  TimedOut,
  TapeSizeExceeded,
  FellLeft,
  FellRight, 
  GoalLeft, 
  GoalRight,
}
use ChunkSimRes::*;

pub fn simulate_on_chunk(
  machine: &SmallBinMachine, 
  mut state: State,
  tape: &mut Tape<Bit>, 
  left_blocked: bool, 
  right_blocked: bool,
  goal_left_len: Option<usize>, 
  goal_right_len: Option<usize>,
  max_steps: u32, 
  max_tape: usize, 
) -> (State, ChunkSimRes) // return tape instead of mutating?
{
  /*
  we check two conditions: 
   1) that neither side is longer than allowed. if there is a goal length, that's the limit, 
      otherwise, the max_tape_size is the limit 
   2) we check the shift left / right from start and ensure it's not larger than some fixed 
      portion of the tape that is live if that side of the tape is "blocked" (this 
      corresponds to running the machine on a tape that doesn't have 0* at the end) 
   */
  // let mut step = 0;
  let print = false;

  let mut disp = 0; 
  let min_left_disp = if left_blocked 
    {Some(-1 * i32::try_from(tape.left_length()).unwrap())} 
    else {None};
  let max_right_disp = if right_blocked 
    {Some(i32::try_from(tape.right_length()).unwrap())} 
    else {None};

  if tape.left_length() > max_tape || tape.right_length() > max_tape {
    panic!("fed in a too long tape to start");
  }
  let left_len_target = goal_left_len.unwrap_or(max_tape);
  let right_len_target = goal_right_len.unwrap_or(max_tape);

  if print {
    println!(
      "step: {} state: {} tape: {}",
      0, state, &tape
    );
  }
  for step in 1..=max_steps {
    let (new_state, dir) = match tape.step_dir(state, machine) {
      Left(edge) => 
        panic!("machine was not fully defined {:?} {} {}", edge, tape, machine.to_compact_format()),
      Right((new_state, dir, steps_taken)) => {
        assert_eq!(steps_taken, 1);
        (new_state, dir.unwrap())
      },
      
    };
    state = new_state;

    disp += dir.to_displacement();
    if print {
      println!(
        "step: {} state: {} tape: {}",
        step, state, &tape
      );
    }

    // check falling off
    if min_left_disp.is_some_and(|min| disp < min) {
      return (state, FellLeft);
    }
    if max_right_disp.is_some_and(|max| disp > max) {
      return (state, FellRight);
    }
    
    // check goal lengths
    if tape.left_length() >= left_len_target {
      assert_eq!(tape.left_length(), left_len_target);
      if left_len_target == max_tape {
        return (state, TapeSizeExceeded);
      } else {
        return (state, GoalLeft);
      }
    }
    if tape.right_length() >= right_len_target {
      assert_eq!(tape.right_length(), right_len_target);
      if right_len_target == max_tape {
        return (state, TapeSizeExceeded);
      } else {
        return (state, GoalRight);
      }
    }
  }
  return (state, TimedOut);
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct BouncerProof {
  x: Vec<Bit>, 
  y: Vec<Bit>, 
  z: Vec<Bit>, 
  state_0: State,
}
impl Display for BouncerProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("BouncerProof x: {} y: {} z: {} state_0: {} ", 
            BL(&self.x), BL(&self.y), BL(&self.z), self.state_0))
    }
}

/*
preconditions: x, y, z are nonempty
returns: either a proof or an error message
*/
pub fn construct_bouncer_proof(machine: &SmallBinMachine, state_0: State, x: &[Bit], y: &[Bit], z: &[Bit])
 -> Result<BouncerProof, &'static str> 
{
  /*
  here's the plan: we want to prove M is a bouncer, specifically that M satisfies
  0* X Z^n Y < 0* 
  becomes 
  0* X Z^(n+1) Y < 0*
  We are given X, Y, Z, so we just need to simulate M on small parts of the tape. 

  0* X Z Z^n Z Y < 0*   sim Z Y < 0* -> < Z1 Y1 0*
  now armed with Z1 and Y1 we're actually going to aim for a slightly different loop
  0* X Z Z^n     < Z1 Y1 0*
  becomes 
  0* X Z Z^(n+1) < Z1 Y1 0*
  via the following process: 
  0* X Z Z^n < Z1 Y1 0*    sim Z < Z1 -> < Z1 Z2
  0* X <  Z1 Z2^n Z2 Y1 0*  sim 0* X < Z1 -> 0* X1 Z3 >
  0* X1 Z3 > Z2^n Z2 Y1 0*  sim Z3 > Z2 -> Z4 Z3 >
  0* X1 Z4 Z4^n Z3 > Y1 0*  sim Z4 Z3 > Y1 0* -> A < B 0* where |B| = |Z1 Y1|
  0* X1 Z4 Z4^(n-1) A  < B  0* (which we hope is equal to)
  0* X Z Z^(n+1) < Z1 Y1 0*
  we can ensure this with the following checks: 
  check states match
  check that B = Z1 Y1 
  check X1 Z4 Z4^(n-1) A = X Z Z^(n+1)
      rewrite n-1 -> n 
      X1 Z4 Z4^n A = X Z Z^(n+2) ( = X Z^(n+1) Z^2 )
      by thm it sufficies to check n=0 n=1
      check (X1 Z4)    A = X Z   (Z Z)
      check (X1 Z4) Z4 A = X Z Z (Z Z)

   */
  /* 
  capabilities needed: 
  * simulate M on [specific tape] until it falls off the [L/R] with the other side 
      [0* / blocked]
  * simulate M on specific tape until it reaches a point where the live left side is
      exactly N long. 
  possible results of simulation: 
      * you hit the desired condition, and the final tape is returned
      * you hit a finite timeout and we give up
      * you fall off the forbidden side of the tape and we give up
      * (maybe) the tape grows too large and we give up
   */
  /*
  note that x, y, and z are the the "left frame", which is to say they start with the 
  thing farthest from the machine head and read towards the machine head. if 
  you want to put something on the right half of the tape, as in Z < Z1, you have to flip it. 
   */
  let print = false;

  let max_steps = 100;
  let max_tape = 50;

  // sim Z Y < 0* -> < Z1 Y1 0*
  if print {
    println!("step 1   sim Z Y < 0* -> < Z1 Y1 0*");
  }
  let mut tape_left = vec![];
  tape_left.extend(z);
  tape_left.extend(y);
  let head = tape_left.pop().unwrap();
  let mut tape : Tape<Bit> = Tape {left: tape_left, head, right: vec![]};
  let (state_1, res) = simulate_on_chunk(
    machine, state_0, &mut tape, 
    true, false, None, None, max_steps, max_tape);
  match res {
    TimedOut => return Err("timed out step 1"),
    TapeSizeExceeded => return Err("taped out step 1"),
    FellLeft => (), // we can continue
    // unreachable: FellRight, GoalLeft, GoalRight
    _ => unreachable!(),
  }
  assert_eq!(tape.head, Bit(false));
  // note that these are reversed due to being on the right. z1 is closest to the head, 
  //which means it's at the *end* of this vec
  let z1y1 = tape.right; 
  if print {
    println!("z1y1 {}", BL(&z1y1));
  }
  if z1y1.len() < z.len() {
    return Err("z1y1 too short");
  }
  //we force length of z1 == length of z 
  // we reverse everything so now they're in the left frame 
  let (z1, y1) = split_first_n(z.len(), &mut z1y1.into_iter().rev());
  if print {
    println!("z1 {} y1 {}", disp_list_bit(&z1), disp_list_bit(&y1));
  }
  
  // sim Z < Z1 -> < Z1 Z2
  if print {
    println!("step 2   sim Z < Z1 -> < Z1 Z2");
  }
  let mut left = z.to_vec();
  let head = left.pop().unwrap();
  // rev since Z1 is on the right
  let right = z1.iter().rev().cloned().collect_vec();
  let mut tape = Tape {left, head, right};
  let (state_2, res) = simulate_on_chunk(
    machine, state_1, &mut tape, 
    true, true, None, None, max_steps, max_tape);
  match res {
    TimedOut => return Err("timed out step 2"),
    TapeSizeExceeded => return Err("taped out step 2"),
    // the hoped for result
    FellLeft => (),
    // the machine went the wrong way
    FellRight => return Err("fell off the wrong side step 2"),
    GoalLeft => unreachable!(),
    GoalRight => unreachable!(),
  }
  assert_eq!(tape.head, Bit(false));
  // extract z1, z2
  let mut mb_z1z2 = tape.right; 
  // to put it in the left frame
  mb_z1z2.reverse();
  if print {
    println!("mbz1z2 {}", disp_list_bit(&mb_z1z2));
    println!("z1 {}", disp_list_bit(&z1));
  }

  assert_eq!(mb_z1z2.len(), z1.len()*2);
  //todo: could rewrite this to use the split helper
  if mb_z1z2[0..z1.len()] != z1 {
    return Err("z1z2 didn't start with z1");
  };
  let z2 = mb_z1z2[z1.len()..2*z1.len()].to_vec();
  if print {
    println!("mb_z1z2 {} z2 {}", BL(&mb_z1z2), BL(&z2));
  }
  
  // sim 0* X < Z1 -> 0* X1 Z3 >
  if print {
    println!("step 3   sim 0* X < Z1 -> 0* X1 Z3 >");
  }
  let mut left = x.to_vec();
  let head = left.pop().unwrap();
  // rev since it's right
  let right = z1.iter().rev().cloned().collect_vec();
  let mut tape = Tape {left, head, right};
  let (state_3, res) = simulate_on_chunk(
    machine, state_2, &mut tape, 
    false, true, None, None, max_steps, max_tape);
  match res {
    TimedOut => return Err("timed out step 3"),
    TapeSizeExceeded => return Err("taped out step 3"),
    FellLeft => unreachable!(),
    FellRight => (),
    GoalLeft => unreachable!(),
    GoalRight => unreachable!(),
  }
  // extract X1 Z3 
  let x1z3 = tape.left;
  if print {
    println!("x1z3 {}", BL(&x1z3));
  }
  if x1z3.len() < z.len() {
    return Err("x1z3 too short")
  }
  let (x1, z3) = split_last_n(z.len(), &mut x1z3.into_iter());
  if print {
    println!("x1 {} z3 {}", BL(&x1), BL(&z3));
  }

  // sim Z3 > Z2 -> Z4 Z3 >
  if print {
    println!("step 4   sim Z3 > Z2 -> Z4 Z3 >");
  }
  let left = z3.clone(); 
  let mut right = z2.iter().rev().cloned().collect_vec();
  let head = right.pop().unwrap();
  let mut tape = Tape {left, head, right};
  let (state_4, res) = simulate_on_chunk(
    machine, state_3, &mut tape, 
    true, true, None, None, max_steps, max_tape);
  match res {
    TimedOut => return Err("timed out step 4"),
    TapeSizeExceeded => return Err("taped out step 4"),
    FellLeft => return Err("fell wrong way step 4"),
    FellRight => (),
    GoalLeft => unreachable!(),
    GoalRight => unreachable!(),
  }
  // extract Z4 Z3 
  let z4z3 = tape.left; 
  assert_eq!(z4z3.len(), z.len()*2);
  let (z4, mb_z3) = split_first_n(z.len(), &mut z4z3.into_iter());
  if mb_z3 != z3 {
    return Err("mb_z3 didn't match z3 in step 4")
  }

  // sim Z4 Z3 > Y1 0* -> A < B 0* where |B| = |Z1 Y1|
  if print {
    println!("step 5   sim Z3 > Y1 0* -> A < B 0* where |B| = |Z1 Y1|");
  }
  let mut left = z4.clone();
  left.extend(&z3);
  let mut right = y1.iter().rev().cloned().collect_vec();
  let head = right.pop().unwrap();
  let mut tape = Tape {left, head, right};
  let goal_right_len = z1.len() + y1.len();
  let (state_5, res) = simulate_on_chunk(
    machine, state_4, &mut tape, 
    true, false, None, Some(goal_right_len), max_steps, max_tape);
  match res {
    TimedOut => return Err("timed out step 5"),
    TapeSizeExceeded => return Err("taped out step 5"),
    FellLeft => return Err("fell left step 5"),
    FellRight => unreachable!(),
    GoalLeft => unreachable!(),
    GoalRight => (),
  }
  let mut b = tape.right;
  b.reverse();
  let mut a = tape.left;
  a.push(tape.head);
  if print {
    println!("a {} b {}", BL(&a), BL(&b));
  }

  //check we are actually in a loop
  if print {
    println!("step 6 (equality checking)");
  }
  // check that final state equals first state
  if state_5 != state_1 {
    return Err("state 5 differed from state 1")
  }
  // check that B = Z1 Y1   
  assert_eq!(b.len(), z1.len()+y1.len());
  let (mb_z1, mb_y1) = split_first_n(z1.len(), &mut b.into_iter()); 
  if print {
    println!("mb_z1 {} mb_y1 {}", BL(&mb_z1), BL(&mb_y1));
  }
  if mb_z1 != z1 {
    return Err("mb_z1 didn't match z1 step 6")
  }
  if mb_y1 != y1 {
    return Err("mb_y1 didn't match y1 step 6")
  }
  if print {
    println!("x1 {} z4 {} a {} x {} z {}", 
      disp_list_bit(&x1),
      disp_list_bit(&z4),
      disp_list_bit(&a),
      disp_list_bit(&x),
      disp_list_bit(&z),
    );
  }
  /*
  check X1 Z4 Z4^n A = X Z Z^(n+1)
      by thm it sufficies to check n=0 n=1
      check (X1 Z4)    A = X Z   (Z Z)
      check (X1 Z4) Z4 A = X Z Z (Z Z)

 */
  let mut x1z4a: Vec<Bit> = vec![];
  x1z4a.extend(&x1);
  x1z4a.extend(&z4);
  x1z4a.extend(&a); 
  let mut xzzz = vec![];
  xzzz.extend(x);
  xzzz.extend(z);
  xzzz.extend(z);
  xzzz.extend(z);
  // this doesn't actually hold; it was proven wrong by 1RB1RH_1RC1RD_1RD1LC_0LC1RB
  // assert_eq!(x1z4a.len(), xzzz.len(), "x1z4a {} xzzz {}", BL(&x1z4a), BL(&xzzz));
  if x1z4a != xzzz {
    return Err("n=0 of loop case failed")
  }

  let mut x1z4z4a: Vec<Bit> = vec![];
  x1z4z4a.extend(&x1);
  x1z4z4a.extend(&z4);
  x1z4z4a.extend(&z4);
  x1z4z4a.extend(&a);
  let mut xzzzz = vec![];
  xzzzz.extend(x);
  xzzzz.extend(z);
  xzzzz.extend(z);
  xzzzz.extend(z);
  xzzzz.extend(z);
  assert_eq!(x1z4z4a.len(), xzzzz.len());
  if x1z4z4a != xzzzz {
    return Err("n=1 of loop case failed")
  }

  let proof = BouncerProof { x: x.to_vec(), y: y.to_vec(), z: z.to_vec(), state_0 };
  return Ok(proof);
}

pub fn try_prove_bouncer(machine: &SmallBinMachine) -> Result<BouncerProof, &'static str> {
  let (x, y, z, state_0) = match find_bouncer_xyz(&machine) {
    Err(s) => return Err(s),
    Ok(ans) => ans,
  };
  construct_bouncer_proof(&machine, state_0, &x, &y, &z)
}

pub type MbBounce = Result<BouncerProof, &'static str>;

pub fn print_mb_proof(mb_proof: &Result<BouncerProof, &str>) -> String{
  match mb_proof {
    Ok(proof) => format!("{}", proof),
    Err(s) => format!("Err: {}", s),
  }
}

mod test {

  use itertools::Itertools;

  use crate::rules::{RS_LEFT, RS_RIGHT};

  use super::*;

  #[test]
  fn test_find_records() {
    // L then R then R then R should give
    // [(0, -1, L), (2, 1, R), (3, 2, R)]
    let inp = vec![RS_LEFT, RS_RIGHT, RS_RIGHT, RS_RIGHT];
    let ans = vec![(0, -1, L), (2, 1, R), (3, 2, R)]
      .into_iter()
      .map(|(a, b, c)| Record(a, b, c))
      .collect_vec();
    let out = find_records(&inp);
    assert_eq!(ans, out);

    /*
    inp
    (0, 5, 2)
    (0, 1, 1)
    (-5, 0, -5)
    (0, 1, 1)
    (-1, 0, -1)
    output
    [(0, 5, R),
     ---
     (2, -2, L)
     ---
     ---
    ]
     */
    let inp = [
      ReadShift { l: 0, r: 5, s: 2 },
      ReadShift { l: 0, r: 1, s: 1 },
      ReadShift { l: -5, r: 0, s: -5 },
      ReadShift { l: 0, r: 1, s: 1 },
      ReadShift { l: -1, r: 0, s: -1 },
    ];
    let ans = vec![(0, 5, R), (2, -2, L)]
      .into_iter()
      .map(|(a, b, c)| Record(a, b, c))
      .collect_vec();
    let out = find_records(&inp);
    assert_eq!(ans, out);
  }
}
