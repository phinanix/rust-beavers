#[allow(unused)]
use either::Either::{self, Left, Right};
use nom::{
  bytes::complete::tag,
  error::{FromExternalError, ParseError},
  sequence::Tuple,
  IResult,
};
use std::{
  fmt::{Debug, Display, Pointer, Write},
  iter::zip,
  num::ParseIntError,
  vec,
};

use crate::{
  rules::{ConsumeGrow, ReadShift, TapeCount},
  turing::{Bit, Dir, Edge, SmallBinMachine, State, TapeSymbol, Trans, Turing, HALT, START},
};

// tape has two stacks and a symbol the machine is currently reading
// since these are array-backed vectors, the "front" is actually at the end
// and the "front" for both the left and the right, is the part which is
// closest to the machine head
// so the turing tape 100 >1< 1110 would be
// vec![1, 0, 0] 1 vec![0, 1, 1, 1]
// the infinite stack of empty symbols is represented implicitly
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Tape<S> {
  left: Vec<S>, //todo: VecDeque?
  head: S,
  right: Vec<S>,
}

pub fn index_from_end<S>(vec: &Vec<S>, length: usize) -> &'_ [S] {
  let len = vec.len();
  &vec[len - length..len]
}

impl<S: TapeSymbol> Tape<S> {
  pub fn new() -> Self {
    Tape {
      left: vec![],
      head: TapeSymbol::empty(),
      right: vec![],
    }
  }

  pub fn left_length(&self) -> usize {
    self.left.len()
  }

  pub fn right_length(&self) -> usize {
    self.right.len()
  }

  pub fn get_slice(&self, leftwards: usize, rightwards: usize) -> (&'_ [S], S, &'_ [S]) {
    let left = index_from_end(&self.left, leftwards);
    let right = index_from_end(&self.right, rightwards);
    return (left, self.head, right);
  }

  pub fn get_displaced_slice(
    &self,
    left: i32,
    right: i32,
    displacement: i32,
  ) -> (&'_ [S], S, &'_ [S]) {
    let left_slice: usize = left.abs_diff(displacement).try_into().unwrap();
    let right_slice: usize = right.abs_diff(displacement).try_into().unwrap();
    self.get_slice(
      left_slice.min(self.left_length()),
      right_slice.min(self.right_length()),
    )
  }

  fn move_right(&mut self) {
    // if the left side is empty and the bit we're moving off is empty, then we can just drop the
    // symbol on the ground since we're adding an empty to the infinite empty stack
    if !(self.left.is_empty() && self.head == TapeSymbol::empty()) {
      self.left.push(self.head);
    }
    self.head = match self.right.pop() {
      Some(s) => s,
      None => TapeSymbol::empty(),
    };
  }

  fn move_left(&mut self) {
    if !(self.right.is_empty() && self.head == TapeSymbol::empty()) {
      self.right.push(self.head);
    }
    self.head = match self.left.pop() {
      Some(s) => s,
      None => TapeSymbol::empty(),
    };
  }

  fn move_dir(&mut self, d: Dir) {
    match d {
      Dir::L => self.move_left(),
      Dir::R => self.move_right(),
    }
  }

  // mutably updates self; returns new state
  // return either new state and the dir we went to get there (Right)
  // or the Edge that the machine couldn't handle (Left)
  pub fn step_dir(&mut self, state: State, t: &impl Turing<S>) -> Either<Edge<S>, (State, Dir)> {
    let edge = Edge(state, self.head);
    let Trans { state, symbol, dir } = match t.step(edge) {
      Some(trans) => trans,
      None => return Left(edge),
    };
    self.head = symbol;
    self.move_dir(dir);
    Right((state, dir))
  }

  // return either new state (Right) or the Edge that the machine couldn't handle (Left)
  pub fn step(&mut self, state: State, t: &impl Turing<S>) -> Either<Edge<S>, State> {
    match self.step_dir(state, t) {
      Left(e) => Left(e),
      Right((s, _d)) => Right(s),
    }
  }

  pub fn simulate(
    &mut self,
    machine: &impl Turing<S>,
    mut state: State,
    num_steps: u32,
    print: bool,
  ) -> (Either<Edge<S>, State>, u32) {
    /* return:
    0: from step
    1: the number of steps executed
     */
    for step in 1..num_steps + 1 {
      state = match self.step(state, machine) {
        Left(edge) => return (Left(edge), step),
        Right(HALT) => return (Right(HALT), step),
        Right(state) => state,
      };
      if print {
        println!("step: {} state: {} tape: {}", step, state, &self);
      }
    }
    (Right(state), num_steps)
  }

  pub fn simulate_from_start(
    machine: &impl Turing<S>,
    num_steps: u32,
    print: bool,
  ) -> (Either<Edge<S>, State>, u32, Self) {
    let mut tape = Self::new();
    let (new_state, num_steps) = tape.simulate(machine, START, num_steps, print);
    (new_state, num_steps, tape)
  }
}

impl Tape<Bit> {
  pub fn from_bools(left: Vec<bool>, head: bool, right: Vec<bool>) -> Self {
    Self {
      left: left.into_iter().map(|b| Bit(b)).collect(),
      head: Bit(head),
      right: right.into_iter().map(|b| Bit(b)).collect(),
    }
  }
}

impl<S: TapeSymbol> Display for Tape<S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for &s in self.left.iter() {
      write!(f, "{}", s)?;
    }
    write!(f, ">{}<", self.head)?;
    for &s in self.right.iter().rev() {
      write!(f, "{}", s)?;
    }
    Ok(())
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ExpTape<S, N> {
  pub left: Vec<(S, N)>,
  pub head: S,
  pub right: Vec<(S, N)>,
  pub tape_end_inf: bool,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Signature<S> {
  pub left: Vec<S>,
  pub head: S,
  pub right: Vec<S>,
}

impl<S: Copy, N: Copy> ExpTape<S, N> {
  pub fn signature(&self) -> Signature<S> {
    let left = self.left.iter().map(|&(s, _n)| s).collect();
    let right = self.right.iter().map(|&(s, _n)| s).collect();
    Signature { left, head: self.head, right }
  }

  // pub fn left(&self) -> &Vec<(S, u32)>
}

impl<S, N> ExpTape<S, N> {
  pub fn map_first<M, F: Fn(N) -> M>(self: Self, f: F) -> ExpTape<S, M> {
    match self {
      Self { left, head, right, tape_end_inf } => ExpTape {
        left: left.into_iter().map(|(s, n)| (s, f(n))).collect(),
        head,
        right: right.into_iter().map(|(s, n)| (s, f(n))).collect(),
        tape_end_inf,
      },
    }
  }

  pub fn map_first_maybe<M, F: Fn(N) -> Option<M>>(self: Self, f: F) -> Option<ExpTape<S, M>> {
    match self {
      Self { left, head, right, tape_end_inf } => Some(ExpTape {
        left: left
          .into_iter()
          .map(|(s, n)| f(n).map(|n| (s, n)))
          .collect::<Option<Vec<(S, M)>>>()?,
        head,
        right: right
          .into_iter()
          .map(|(s, n)| f(n).map(|n| (s, n)))
          .collect::<Option<Vec<(S, M)>>>()?,
        tape_end_inf,
      }),
    }
  }

  pub fn map_second<T, F: Fn(S) -> T>(self: Self, f: F) -> ExpTape<T, N> {
    match self {
      Self { left, head, right, tape_end_inf } => ExpTape {
        left: left.into_iter().map(|(s, n)| (f(s), n)).collect(),
        head: f(head),
        right: right.into_iter().map(|(s, n)| (f(s), n)).collect(),
        tape_end_inf,
      },
    }
  }
}

impl<S: TapeSymbol, C: TapeCount> ExpTape<S, C> {
  pub fn new(tape_end_inf: bool) -> Self {
    ExpTape {
      left: vec![],
      head: TapeSymbol::empty(),
      right: vec![],
      tape_end_inf,
    }
  }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum TapeChangeKind {
  Grew,
  Shrunk,
}
use TapeChangeKind::*;

pub fn combine_one_step_tape_change(tc1: TapeChange, tc2: TapeChange) -> TapeChange {
  match (tc1, tc2) {
    (None, _) => tc2,
    (_, None) => tc1,
    (Some((_d1, tc1)), Some((_d2, tc2))) => {
      assert_eq!((tc1, tc2), (Shrunk, Grew));
      None
    }
  }
}

pub type TapeChange = Option<(Dir, TapeChangeKind)>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepResult<S> {
  UndefinedEdge(Edge<S>),
  FellOffTape(Dir),
  Success(State, ReadShift),
}
use StepResult::*;

impl<S> StepResult<S> {
  pub fn expect_success(self) -> (State, ReadShift) {
    match self {
      Success(state, rs) => (state, rs),
      _ => panic!("success was expected"),
    }
  }
}

impl<S: TapeSymbol, C: TapeCount> ExpTape<S, C> {
  // impl<S: TapeSymbol> ExpTape<S, u32> {
  fn push_rle(stack: &mut Vec<(S, C)>, item: S, tape_end_inf: bool) -> Option<TapeChangeKind> {
    match stack.last_mut() {
      // if the stack is empty and the symbol we're pushing is empty, then we can just drop the
      // symbol on the ground since we're adding an empty to the infinite empty stack
      // if so, we return Shrunk to indicate we did that, else None
      None => {
        if item != TapeSymbol::empty() || !tape_end_inf {
          stack.push((item, 1.into()));
          None
        } else {
          Some(TapeChangeKind::Shrunk)
        }
      }
      Some((s, count)) => {
        if item == *s {
          *count = C::add(*count, 1.into());
        } else {
          stack.push((item, 1.into()));
        }
        None
      }
    }
  }

  fn pop_rle(stack: &mut Vec<(S, C)>, tape_end_inf: bool) -> Option<(S, Option<TapeChangeKind>)> {
    // if we grew the tape from the edge, return Some(Grew), else None
    let ans = match stack.last_mut() {
      None => {
        if !tape_end_inf {
          return None;
        } else {
          return Some((TapeSymbol::empty(), Some(TapeChangeKind::Grew)));
        };
      }
      Some((s, count)) => {
        *count = C::sub_one(*count);
        *s
      }
    };
    match stack.last() {
      Some(&(_s, c)) if c == C::zero() => {
        stack.pop();
      }
      _ => (),
    }
    return Some((ans, None));
  }

  fn move_right(&mut self) -> Option<TapeChange> {
    let tc1 = Self::push_rle(&mut self.left, self.head, self.tape_end_inf).map(|tc| (Dir::L, tc));
    let (new_head, tck2) = Self::pop_rle(&mut self.right, self.tape_end_inf)?;
    let tc2 = tck2.map(|tc| (Dir::R, tc));
    self.head = new_head;
    Some(combine_one_step_tape_change(tc1, tc2))
  }

  fn move_left(&mut self) -> Option<TapeChange> {
    let tc1 = Self::push_rle(&mut self.right, self.head, self.tape_end_inf).map(|tc| (Dir::R, tc));
    let (new_head, tck2) = Self::pop_rle(&mut self.left, self.tape_end_inf)?;
    let tc2 = tck2.map(|tc| (Dir::L, tc));
    self.head = new_head;
    Some(combine_one_step_tape_change(tc1, tc2))
  }

  fn move_dir(&mut self, d: Dir) -> Option<TapeChange> {
    match d {
      Dir::L => self.move_left(),
      Dir::R => self.move_right(),
    }
  }

  //todo: these 3 functions are duplicated, some chance we want to dedub with Tape, not sure
  pub fn step_extra_info(&mut self, state: State, t: &impl Turing<S>) -> StepResult<S> {
    // returns left when there is an exceptional condition
    //  - returns an edge if that edge is not defined
    //  - returns a dir if the machine attempted to move off that dir (if the tape is finite)
    // extra info: tape grew, shrank or nothing, on the L/R
    let edge = Edge(state, self.head);
    let Trans { state, symbol, dir } = match t.step(edge) {
      Some(trans) => trans,
      None => return UndefinedEdge(edge),
    };
    self.head = symbol;
    match self.move_dir(dir) {
      Some(_tc) => (),
      None => return FellOffTape(dir),
    };
    let rs = ReadShift::rs_in_dir(dir);
    Success(state, rs)
  }

  fn simulate(
    &mut self,
    machine: &impl Turing<S>,
    mut state: State,
    num_steps: u32,
  ) -> (Either<Edge<S>, State>, u32) {
    /* return:
    0: from step
    1: the number of steps executed
     */
    for step in 1..num_steps + 1 {
      state = match self.step_extra_info(state, machine) {
        UndefinedEdge(edge) => return (Left(edge), step),
        Success(HALT, _) => return (Right(HALT), step),
        Success(state, _) => state,
        FellOffTape(_) => panic!("unexpectedly fell off tape!"),
      };
      println!("step: {} phase: {} tape: {}", step, state, self);
    }
    (Right(state), num_steps)
  }
}

impl<S: TapeSymbol> ExpTape<S, u32> {
  pub fn simulate_from_start(
    machine: &impl Turing<S>,
    num_steps: u32,
  ) -> (Either<Edge<S>, State>, u32, Self) {
    let mut tape = Self::new(true);
    let (new_state, num_steps) = tape.simulate(machine, START, num_steps);
    (new_state, num_steps, tape)
  }

  fn splat(rle_vec: &Vec<(S, u32)>) -> Vec<S> {
    let mut out = vec![];
    for &(symbol, count) in rle_vec {
      for _ in 0..count {
        out.push(symbol);
      }
    }
    out
  }

  fn to_tape(ExpTape { left, head, right, tape_end_inf }: &ExpTape<S, u32>) -> Tape<S> {
    assert!(tape_end_inf);
    Tape {
      left: Self::splat(left),
      head: *head,
      right: Self::splat(right),
    }
  }

  pub fn numbers_too_large(&self) -> bool {
    let Self { left, head: _, right, tape_end_inf: _ } = self;
    let too_large = 10_000_000;
    left
      .iter()
      .chain(right.iter())
      .any(|&(_s, n)| n > too_large)
  }
}

//currently used only for Display
pub struct TapeHalf<'a, S, C>(pub Dir, pub &'a Vec<(S, C)>);

impl<'a, S: TapeSymbol, C: Display> Display for TapeHalf<'a, S, C> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self.0 {
      Dir::L => {
        for (s, n) in self.1.iter() {
          write!(f, "({}, {}) ", s, n)?;
        }
      }
      Dir::R => {
        for (s, n) in self.1.iter().rev() {
          write!(f, " ({}, {})", s, n)?;
        }
      }
    };
    Ok(())
  }
}

impl<S: TapeSymbol, C: TapeCount> Display for ExpTape<S, C> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", TapeHalf(Dir::L, &self.left))?;
    // for &(s, n) in self.left.iter() {
    //   write!(f, "({}, {}) ", s, n)?;
    // }
    write!(f, "|>{}<|", self.head)?;
    write!(f, "{}", TapeHalf(Dir::R, &self.right))?;
    // for &(s, n) in self.right.iter().rev() {
    //   write!(f, " ({}, {})", s, n)?;
    // }
    Ok(())
  }
}

impl ExpTape<Bit, u32> {
  pub fn from_bools(
    left: Vec<(bool, u32)>,
    head: bool,
    right: Vec<(bool, u32)>,
    tape_end_inf: bool,
  ) -> Self {
    Self {
      left: left.into_iter().map(|(b, n)| (Bit(b), n)).collect(),
      head: Bit(head),
      right: right.into_iter().map(|(b, n)| (Bit(b), n)).collect(),
      tape_end_inf,
    }
  }
}

pub fn tnf_simulate(inp_machine: SmallBinMachine, total_steps: u32) -> Vec<SmallBinMachine> {
  let mut out = vec![];

  struct TnfState {
    machine: SmallBinMachine,
    state: State,
    tape: Tape<Bit>,
    num_steps: u32,
  }

  let mut stack = vec![TnfState {
    machine: inp_machine,
    state: START,
    tape: Tape::new(),
    num_steps: 0,
  }];
  while let Some(TnfState { machine, state, mut tape, num_steps }) = stack.pop() {
    match tape.simulate(&machine, state, total_steps - num_steps, false) {
      (Right(_state), _simulated_steps) => out.push(machine),
      (Left(edge), simulated_steps) => {
        let new_state = edge.0;
        let new_step_total = simulated_steps + num_steps;
        let new_machines = machine.branch_on_edge(edge);
        for machine in new_machines {
          stack.push(TnfState {
            machine,
            state: new_state,
            tape: tape.clone(),
            num_steps: new_step_total,
          });
        }
      }
    }
  }

  out
}

mod test {
  use super::*;
  use crate::{
    parse::{parse_avar_gen, parse_rule, parse_tape},
    rules::{RS_LEFT, RS_RIGHT},
    turing::{get_machine, HALT},
  };

  #[test]
  fn step_extra_info() {
    // ("binary_counter", "0LB0RA_1LC1LH_1RA1LC"),
    // we want a grow, shrink, nothing, both in both directions ideally
    // nothing: B T >F<
    // grow:    B   >F< F
    // shrink:  A T >F<
    // both:    A   >F<
    let machine = get_machine("binary_counter");

    //1LC
    let mut nothing_tape = parse_tape("(T, 2) |>F<| ").unwrap().1;
    let res = nothing_tape.step_extra_info(State(2), &machine);
    assert_eq!(res, Success(State(3), RS_LEFT));
    assert_eq!(nothing_tape, parse_tape("(T, 1) |>T<| (T, 1)").unwrap().1);

    //1LC
    let mut grow_tape = parse_tape(" |>F<| (F, 1)").unwrap().1;
    let res = grow_tape.step_extra_info(State(2), &machine);
    assert_eq!(res, Success(State(3), RS_LEFT));
    assert_eq!(grow_tape, parse_tape(" |>F<| (T, 1) (F, 1)").unwrap().1);

    //0LB
    let mut shrink_tape = parse_tape("(T, 1) |>F<| ").unwrap().1;
    let res = shrink_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(2), RS_LEFT));
    assert_eq!(shrink_tape, parse_tape(" |>T<| ").unwrap().1);

    //0LB
    let mut both_tape = parse_tape(" |>F<| ").unwrap().1;
    let res = both_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(2), RS_LEFT));
    assert_eq!(both_tape, parse_tape(" |>F<| ").unwrap().1);

    //1RA
    let mut nothing2_tape = parse_tape("(T, 2) |>F<| (F, 1) (T, 1)").unwrap().1;
    let res = nothing2_tape.step_extra_info(State(3), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT));
    assert_eq!(nothing2_tape, parse_tape("(T, 3) |>F<| (T, 1)").unwrap().1);

    //0RA
    let mut grow2_tape = parse_tape("(T, 1) |>T<| ").unwrap().1;
    let res = grow2_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT));
    assert_eq!(grow2_tape, parse_tape("(T, 1) (F, 1) |>F<| ").unwrap().1);

    //0RA
    let mut shrink2_tape = parse_tape(" |>T<| (T, 1)").unwrap().1;
    let res = shrink2_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT));
    assert_eq!(shrink2_tape, parse_tape(" |>T<| ").unwrap().1);

    //0RA
    let mut both_tape = parse_tape(" |>T<| ").unwrap().1;
    let res = both_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT));
    assert_eq!(both_tape, parse_tape(" |>F<| ").unwrap().1);
  }

  #[test]
  fn exptape_to_tape() {
    let e_tape = ExpTape::from_bools(
      vec![(true, 2), (false, 1)],
      false,
      vec![(true, 1), (false, 3), (true, 1)],
      true,
    );
    let tape = Tape::from_bools(
      vec![true, true, false],
      false,
      vec![true, false, false, false, true],
    );
    assert_eq!(ExpTape::to_tape(&e_tape), tape)
  }
  #[test]
  fn sim_bb2() {
    let bb2 = get_machine("bb2");
    let (state, num_steps, tape) = Tape::simulate_from_start(&bb2, 10, false);
    assert_eq!(state, Right(HALT));
    assert_eq!(num_steps, 6);
    assert_eq!(tape, Tape::from_bools(vec![true, true], true, vec![true]));
    let (e_state, e_steps, e_tape) = ExpTape::simulate_from_start(&bb2, 10);
    assert_eq!(
      (e_state, e_steps, ExpTape::to_tape(&e_tape)),
      (state, num_steps, tape)
    );
  }
  #[test]
  fn sim_bb3() {
    let bb3 = get_machine("bb3");
    let (state, num_steps, tape) = Tape::simulate_from_start(&bb3, 30, false);
    assert_eq!(state, Right(HALT));
    assert_eq!(num_steps, 14);
    assert_eq!(
      tape,
      Tape::from_bools(vec![true, true, true], true, vec![true, true])
    );
    let (e_state, e_steps, e_tape) = ExpTape::simulate_from_start(&bb3, 30);
    assert_eq!(
      (e_state, e_steps, ExpTape::to_tape(&e_tape)),
      (state, num_steps, tape)
    );
  }
  //todo: simulate bb4 to further sanity check

  //tests to write: bb4
  // match var num, match rule tape, append rule tape, apply rule, apply rules,
}
