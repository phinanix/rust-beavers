use either::{
  Either,
  Either::{Left, Right},
};

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

/*
 parameters: &[ReadShift], the list of readshifts
 returns:   Vec<(usize, i32, Dir)> which is
 (timestamp of record, record distance, record direction)
*/

pub fn find_records(readshifts: &[ReadShift]) -> Vec<(usize, i32, Dir)> {
  let mut cur_rs = ReadShift { l: 0, r: 0, s: 0 };
  let mut out = vec![];
  for (i, &new_rs) in readshifts.into_iter().enumerate() {
    let prev_rs = cur_rs;
    cur_rs = ReadShift::normalize(ReadShift::combine(cur_rs, new_rs));
    if cur_rs.l < prev_rs.l {
      out.push((i, cur_rs.l, Dir::L));
    }
    if cur_rs.r > prev_rs.r {
      out.push((i, cur_rs.r, Dir::R));
    }
  }
  out
}
/*
  returns:
  Left: the step at which the machine was infinite
  or
  Right:
   the tape history, which is a
  Vec<(u32, P, ExpTape<S, u32>)> which is (steps, phase, tape)
  and the Vec<ReadShift>

*/
pub fn get_records_for_machine<P: Phase, S: TapeSymbol>(
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

mod test {

  use crate::rules::{RS_LEFT, RS_RIGHT};

  use super::*;

  #[test]
  fn test_find_records() {
    // L then R then R then R should give
    // [(0, -1, L), (2, 1, R), (3, 2, R)]
    let inp = vec![RS_LEFT, RS_RIGHT, RS_RIGHT, RS_RIGHT];
    let ans = vec![(0, -1, L), (2, 1, R), (3, 2, R)];
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
    let ans = vec![(0, 5, R), (2, -2, L)];
    let out = find_records(&inp);
    assert_eq!(ans, out);
  }
}
