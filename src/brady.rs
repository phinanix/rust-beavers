use std::{fmt::Display, ops::Sub};

use crate::{
  rules::{ReadShift, Rulebook},
  simulate::{one_rule_step, RuleStepResult::*},
  tape::ExpTape,
  turing::{
    Dir,
    Dir::{L, R},
    Phase, TapeSymbol, Turing,
  },
};
use either::{
  Either,
  Either::{Left, Right},
};
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
  let mut prev_record = *records.next().unwrap();
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

pub fn difference_of<T: CheckedSub + Copy>(xs: &[T]) -> Vec<T> {
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
