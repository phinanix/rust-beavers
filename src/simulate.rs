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

use crate::turing::{
  Bit, Dir, Edge, SmallBinMachine, State, TapeSymbol, Trans, Turing, HALT, START,
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

impl<S: TapeSymbol> ExpTape<S, u32> {
  pub fn new() -> Self {
    ExpTape {
      left: vec![],
      head: TapeSymbol::empty(),
      right: vec![],
    }
  }

  fn push_rle(stack: &mut Vec<(S, u32)>, item: S) {
    match stack.last_mut() {
      // if the stack is empty and the symbol we're pushing is empty, then we can just drop the
      // symbol on the ground since we're adding an empty to the infinite empty stack
      None => {
        if item != TapeSymbol::empty() {
          stack.push((item, 1))
        }
      }
      Some((s, count)) => {
        if item == *s {
          *count += 1;
        } else {
          stack.push((item, 1));
        }
      }
    }
  }

  fn pop_rle(stack: &mut Vec<(S, u32)>) -> S {
    let ans = match stack.last_mut() {
      None => return TapeSymbol::empty(),
      Some((s, count)) => {
        *count -= 1;
        *s
      }
    };
    if let Some((_s, 0)) = stack.last() {
      stack.pop();
    }
    return ans;
  }

  fn move_right(&mut self) {
    Self::push_rle(&mut self.left, self.head);
    self.head = Self::pop_rle(&mut self.right);
  }

  fn move_left(&mut self) {
    Self::push_rle(&mut self.right, self.head);
    self.head = Self::pop_rle(&mut self.left);
  }

  fn move_dir(&mut self, d: Dir) {
    match d {
      Dir::L => self.move_left(),
      Dir::R => self.move_right(),
    }
  }

  //todo: these 3 functions are duplicated, some chance we want to dedub with Tape, not sure
  pub fn step(&mut self, state: State, t: &impl Turing<S>) -> Either<Edge<S>, State> {
    let edge = Edge(state, self.head);
    let Trans { state, symbol, dir } = match t.step(edge) {
      Some(trans) => trans,
      None => return Left(edge),
    };
    self.head = symbol;
    self.move_dir(dir);
    Right(state)
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
      state = match self.step(state, machine) {
        Left(edge) => return (Left(edge), step),
        Right(HALT) => return (Right(HALT), step),
        Right(state) => state,
      };
      println!("step: {} phase: {} tape: {}", step, state, self);
    }
    (Right(state), num_steps)
  }

  pub fn simulate_from_start(
    machine: &impl Turing<S>,
    num_steps: u32,
  ) -> (Either<Edge<S>, State>, u32, Self) {
    let mut tape = Self::new();
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

  fn to_tape(ExpTape { left, head, right }: &ExpTape<S, u32>) -> Tape<S> {
    Tape {
      left: Self::splat(left),
      head: *head,
      right: Self::splat(right),
    }
  }
}

impl<S: TapeSymbol> Display for ExpTape<S, u32> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for &(s, n) in self.left.iter() {
      write!(f, "({}, {}) ", s, n)?;
    }
    write!(f, "|>{}<|", self.head)?;
    for &(s, n) in self.right.iter().rev() {
      write!(f, " ({}, {})", s, n)?;
    }
    Ok(())
  }
}

impl ExpTape<Bit, u32> {
  pub fn from_bools(left: Vec<(bool, u32)>, head: bool, right: Vec<(bool, u32)>) -> Self {
    Self {
      left: left.into_iter().map(|(b, n)| (Bit(b), n)).collect(),
      head: Bit(head),
      right: right.into_iter().map(|(b, n)| (Bit(b), n)).collect(),
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
    rules::parse::{parse_avar, parse_rule},
    turing::{get_machine, HALT},
  };

  #[test]
  fn exptape_to_tape() {
    let e_tape = ExpTape::from_bools(
      vec![(true, 2), (false, 1)],
      false,
      vec![(true, 1), (false, 3), (true, 1)],
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
