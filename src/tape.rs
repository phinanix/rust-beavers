#[allow(unused)]
use either::Either::{self, Left, Right};

use std::{
  fmt::{Debug, Display},
  ops::AddAssign,
  vec,
};

use crate::{
  rules::{ReadShift, TapeCount},
  turing::{Bit, Dir, Edge, Phase, SmallBinMachine, State, TapeSymbol, Trans::*, Turing},
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
  pub left: Vec<S>, //todo: VecDeque?
  pub head: S,
  pub right: Vec<S>,
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
  pub fn to_list(&self) -> Vec<S> {
    let mut out = vec![];
    out.extend(self.left.iter());
    out.push(self.head);
    out.extend(self.right.iter().rev());
    out
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

    // temporarily disabling that feature because it made LR detection wrong :0
    // LR detection was actually right I think but leaving the feature disabled
    // if !(self.left.is_empty() && self.head == TapeSymbol::empty()) {
    self.left.push(self.head);
    // } else {
    // println!("\n DROP\nDROP\nDROP\n")
    // }
    self.head = match self.right.pop() {
      Some(s) => s,
      None => TapeSymbol::empty(),
    };
  }

  fn move_left(&mut self) {
    // if !(self.right.is_empty() && self.head == TapeSymbol::empty()) {
    self.right.push(self.head);
    // }
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
  // return either new state, the dir we went to get there, and the steps taken (Right)
  // or the Edge that the machine couldn't handle (Left)
  pub fn step_dir<P: Phase>(
    &mut self,
    state: P,
    t: &impl Turing<P, S>,
  ) -> Either<Edge<P, S>, (P, Option<Dir>, u32)> {
    let edge = Edge(state, self.head);
    let (state, symbol, mb_dir, steps) = match t.step(edge) {
      Some(Step { state, symbol, dir, steps }) => (state, symbol, Some(dir), steps),
      Some(Halt { state, symbol, mb_dir, steps }) => (state, symbol, mb_dir, steps),
      Some(Infinite) => return Right((P::INFINITE, None, 0)),
      None => return Left(edge),
    };
    self.head = symbol;
    if let Some(dir) = mb_dir {
      self.move_dir(dir);
    }
    Right((state, mb_dir, steps))
  }

  // return either new state (Right) or the Edge that the machine couldn't handle (Left)
  pub fn step<P: Phase>(
    &mut self,
    state: P,
    t: &impl Turing<P, S>,
  ) -> Either<Edge<P, S>, (P, u32)> {
    match self.step_dir(state, t) {
      Left(e) => Left(e),
      Right((s, _d, steps)) => Right((s, steps)),
    }
  }

  pub fn simulate<P: Phase>(
    &mut self,
    machine: &impl Turing<P, S>,
    mut state: P,
    num_simulator_steps: u32,
    print: bool,
  ) -> (Either<Edge<P, S>, P>, u32) {
    /* return:
    0: from step
    1: the number of steps executed
     */
    let mut machine_steps = 0;
    for step in 1..num_simulator_steps + 1 {
      state = match self.step(state, machine) {
        Left(edge) => return (Left(edge), step),
        Right((state, steps)) => {
          machine_steps += steps;
          if state.halted() {
            return (Right(state), machine_steps);
          }
          state
        }
      };
      if print {
        println!(
          "step: {} machine_step: {} state: {} tape: {}",
          step, machine_steps, state, &self
        );
      }
    }
    (Right(state), machine_steps)
  }

  pub fn simulate_from_start<P: Phase>(
    machine: &impl Turing<P, S>,
    num_steps: u32,
    print: bool,
  ) -> (Either<Edge<P, S>, P>, u32, Self) {
    let mut tape = Self::new();
    let (new_state, num_steps) = tape.simulate(machine, P::START, num_steps, print);
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

pub fn disp_list_bit(bits: &[Bit]) -> String {
  let mut out = String::new();
  for b in bits {
    out.push_str(&b.to_string())
  }
  out
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

//  UndefinedEdge: an edge if that edge is not defined
//  FellOffTape: returns a dir if the machine attempted to move off that dir (if the tape is finite)
//  Success: the new state, plus the one-step-readshift

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepResult<P, S> {
  UndefinedEdge(Edge<P, S>),
  SRInfinite,
  FellOffTape(P, Dir, u32),
  Success(P, ReadShift, u32),
}
use StepResult::*;

impl<P, S> StepResult<P, S> {
  pub fn expect_success(self) -> (P, ReadShift, u32) {
    match self {
      Success(state, rs, steps) => (state, rs, steps),
      _ => panic!("success was expected"),
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

  pub fn push_rle(stack: &mut Vec<(S, C)>, item: S, _tape_end_inf: bool) {
    match stack.last_mut() {
      // if the stack is empty and the symbol we're pushing is empty, then we can just drop the
      // symbol on the ground since we're adding an empty to the infinite empty stack
      // temp disabling this feature, see Tape
      None => {
        // if item != TapeSymbol::empty() || !tape_end_inf {
        stack.push((item, 1.into()));
      }
      Some((s, count)) => {
        if item == *s {
          *count = C::add(*count, 1.into());
        } else {
          stack.push((item, 1.into()));
        }
      }
    }
  }

  fn pop_rle(stack: &mut Vec<(S, C)>, tape_end_inf: bool) -> Option<S> {
    // if we grew the tape from the edge, return Some(Grew), else None
    let ans = match stack.last_mut() {
      None => {
        if !tape_end_inf {
          return None;
        } else {
          return Some(TapeSymbol::empty());
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
    return Some(ans);
  }

  fn move_right(&mut self) -> Option<()> {
    Self::push_rle(&mut self.left, self.head, self.tape_end_inf);
    self.head = Self::pop_rle(&mut self.right, self.tape_end_inf)?;
    Some(())
  }

  fn move_left(&mut self) -> Option<()> {
    Self::push_rle(&mut self.right, self.head, self.tape_end_inf);
    self.head = Self::pop_rle(&mut self.left, self.tape_end_inf)?;
    Some(())
  }

  fn move_dir(&mut self, d: Dir) -> Option<()> {
    match d {
      Dir::L => self.move_left(),
      Dir::R => self.move_right(),
    }
  }

  //todo: these 3 functions are duplicated, some chance we want to dedub with Tape, not sure
  pub fn step_extra_info<P: Phase>(&mut self, state: P, t: &impl Turing<P, S>) -> StepResult<P, S> {
    let edge = Edge(state, self.head);
    let (state, symbol, mb_dir, steps) = match t.step(edge) {
      Some(Infinite) => return SRInfinite,
      Some(Halt { state, symbol, mb_dir, steps }) => (state, symbol, mb_dir, steps),
      Some(Step { state, symbol, dir, steps }) => (state, symbol, Some(dir), steps),
      None => return UndefinedEdge(edge),
    };
    self.head = symbol;
    match mb_dir {
      None => {
        assert!(state.halted());
        Success(state, ReadShift { l: 0, r: 0, s: 0 }, steps)
      }
      Some(dir) => {
        match self.move_dir(dir) {
          Some(()) => (),
          None => return FellOffTape(state, dir, steps),
        };
        let rs = ReadShift::rs_in_dir(dir);
        Success(state, rs, steps)
      }
    }
  }

  fn simulate<P: Phase>(
    &mut self,
    machine: &impl Turing<P, S>,
    mut state: P,
    num_simulator_steps: u32,
  ) -> (Either<Edge<P, S>, P>, u32) {
    /* return:
    0: from step
    1: the number of steps executed
     */
    let mut machine_steps = 0;
    for step in 1..num_simulator_steps + 1 {
      state = match self.step_extra_info(state, machine) {
        UndefinedEdge(edge) => return (Left(edge), step),
        Success(state, _, steps) => {
          machine_steps += steps;
          if state.halted() {
            return (Right(state), machine_steps);
          }
          state
        }
        SRInfinite => return (Right(P::INFINITE), machine_steps),
        FellOffTape(_, _, _) => panic!("unexpectedly fell off tape!"),
      };
      println!("step: {} phase: {} tape: {}", step, state, self);
    }
    (Right(state), machine_steps)
  }
}

impl<'a, S: TapeSymbol + 'a> ExpTape<S, u32> {
  pub fn simulate_from_start<P: Phase>(
    machine: &impl Turing<P, S>,
    num_steps: u32,
  ) -> (Either<Edge<P, S>, P>, u32, Self) {
    let mut tape = Self::new(true);
    let (new_state, num_steps) = tape.simulate(machine, P::START, num_steps);
    (new_state, num_steps, tape)
  }

  pub fn splat(rle_vec: &mut impl Iterator<Item = &'a (S, u32)>) -> Vec<S> {
    let mut out = vec![];
    for &(symbol, count) in rle_vec {
      for _ in 0..count {
        out.push(symbol.clone());
      }
    }
    out
  }

  pub fn un_splat(not_rle: &mut impl Iterator<Item = &'a S>, tape_end_inf: bool) -> Vec<(S, u32)> {
    let mut out = vec![];
    for &s in not_rle {
      ExpTape::push_rle(&mut out, s, tape_end_inf);
    }
    out
  }

  pub fn to_tape(ExpTape { left, head, right, tape_end_inf }: &ExpTape<S, u32>) -> Tape<S> {
    assert!(tape_end_inf);
    Tape {
      left: Self::splat(&mut left.iter()),
      head: *head,
      right: Self::splat(&mut right.iter()),
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

  pub fn left_len(&self) -> u32 {
    self.left.iter().map(|(_s, n)| n).sum()
  }

  pub fn right_len(&self) -> u32 {
    self.right.iter().map(|(_s, n)| n).sum()
  }

  pub fn len(&self) -> u32 {
    // let Self { left, head: _, right, tape_end_inf: _ } = self;
    // let l_sum: u32 = left.iter().map(|(_s, n)| n).sum();
    // let r_sum: u32 = right.iter().map(|(_s, n)| n).sum();
    self.left_len() + self.right_len() + 1
    // l_sum + r_sum + 1
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

pub fn tnf_simulate(
  inp_machine: SmallBinMachine,
  total_steps: u32,
  allow_no_halt: bool,
) -> Vec<SmallBinMachine> {
  let mut out = vec![];

  struct TnfState {
    machine: SmallBinMachine,
    state: State,
    tape: Tape<Bit>,
    num_steps: u32,
  }

  let mut stack = vec![TnfState {
    machine: inp_machine,
    state: State::START,
    tape: Tape::new(),
    num_steps: 0,
  }];
  while let Some(TnfState { machine, state, mut tape, num_steps }) = stack.pop() {
    if out.len() > 0 && out.len() % 1_000_000 == 0 {
      println!("tnf machines {}", out.len());
    }
    match tape.simulate(&machine, state, total_steps - num_steps, false) {
      (Right(_state), _simulated_steps) => out.push(machine),
      (Left(edge), simulated_steps) => {
        let new_state = edge.0;
        let new_step_total = simulated_steps + num_steps;
        let new_machines = machine.branch_on_edge(edge, allow_no_halt);
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

pub fn push_exptape<S: Eq, C: AddAssign>(tape: &mut Vec<(S, C)>, item: (S, C)) {
  match tape.last_mut() {
    None => tape.push(item),
    Some((tape_s, tape_c)) => {
      if *tape_s == item.0 {
        *tape_c += item.1;
      } else {
        tape.push(item);
      }
    }
  }
}

#[cfg(test)]
mod test {
  use itertools::Itertools;

  use super::*;
  use crate::{
    parse::parse_tape,
    rules::{RS_LEFT, RS_RIGHT},
    turing::HALT,
    turing_examples::get_machine,
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
    assert_eq!(res, Success(State(3), RS_LEFT, 1));
    assert_eq!(nothing_tape, parse_tape("(T, 1) |>T<| (T, 1)").unwrap().1);

    //1LC
    let mut grow_tape = parse_tape(" |>F<| (F, 1)").unwrap().1;
    let res = grow_tape.step_extra_info(State(2), &machine);
    assert_eq!(res, Success(State(3), RS_LEFT, 1));
    assert_eq!(grow_tape, parse_tape(" |>F<| (T, 1) (F, 1)").unwrap().1);

    //0LB
    let mut shrink_tape = parse_tape("(T, 1) |>F<| ").unwrap().1;
    let res = shrink_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(2), RS_LEFT, 1));
    assert_eq!(shrink_tape, parse_tape(" |>T<| (F, 1)").unwrap().1);

    //0LB
    let mut both_tape = parse_tape(" |>F<| ").unwrap().1;
    let res = both_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(2), RS_LEFT, 1));
    assert_eq!(both_tape, parse_tape(" |>F<| (F, 1)").unwrap().1);

    //1RA
    let mut nothing2_tape = parse_tape("(T, 2) |>F<| (F, 1) (T, 1)").unwrap().1;
    let res = nothing2_tape.step_extra_info(State(3), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT, 1));
    assert_eq!(nothing2_tape, parse_tape("(T, 3) |>F<| (T, 1)").unwrap().1);

    //0RA
    let mut grow2_tape = parse_tape("(T, 1) |>T<| ").unwrap().1;
    let res = grow2_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT, 1));
    assert_eq!(grow2_tape, parse_tape("(T, 1) (F, 1) |>F<| ").unwrap().1);

    //0RA
    let mut shrink2_tape = parse_tape(" |>T<| (T, 1)").unwrap().1;
    let res = shrink2_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT, 1));
    assert_eq!(shrink2_tape, parse_tape("(F, 1) |>T<| ").unwrap().1);

    //0RA
    let mut both_tape = parse_tape(" |>T<| ").unwrap().1;
    let res = both_tape.step_extra_info(State(1), &machine);
    assert_eq!(res, Success(State(1), RS_RIGHT, 1));
    assert_eq!(both_tape, parse_tape("(F, 1) |>F<| ").unwrap().1);
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

  #[test]
  fn tape_to_list() {
    // you pop from the *end* of the vec because it's an array backed vec.
    let tape = Tape::from_bools(vec![false, true], true, vec![false, true]);
    let list = tape.to_list();
    let ans = vec![false, true, true, true, false]
      .into_iter()
      .map(|b| Bit(b))
      .collect_vec();
    assert_eq!(list, ans);
  }
  //todo: simulate bb4 to further sanity check

  //tests to write: bb4
  // match var num, match rule tape, append rule tape, apply rule, apply rules,
}
