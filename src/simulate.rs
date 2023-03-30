#[allow(unused)]
use either::Either::{self, Left, Right};
use std::{fmt::Debug, vec};

use crate::turing::{Dir, Edge, SmallBinMachine, State, Trans, Turing, HALT, START};

trait TapeSymbol: Copy + Eq + Debug {
  fn empty() -> Self;
}

impl TapeSymbol for bool {
  fn empty() -> Self {
    false
  }
}

// tape has two stacks and a symbol the machine is currently reading
// since these are array-backed vectors, the "front" is actually at the end
// and the "front" for both the left and the right, is the part which is
// closest to the machine head
// so the turing tape 100 >1< 1110 would be
// vec![1, 0, 0] 1 vec![0, 1, 1, 1]
// the infinite stack of empty symbols is represented implicitly
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Tape<S> {
  left: Vec<S>,
  head: S,
  right: Vec<S>,
}

impl<S: TapeSymbol> Tape<S> {
  fn new() -> Self {
    Tape {
      left: vec![],
      head: TapeSymbol::empty(),
      right: vec![],
    }
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
  // return either final state (Right) or the Edge that the machine couldn't handle (Left)
  fn step(&mut self, state: State, t: &impl Turing<S>) -> Either<Edge<S>, State> {
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
      // dbg!(&self, state);
    }
    (Right(state), num_steps)
  }

  fn simulate_from_start(
    machine: &impl Turing<S>,
    num_steps: u32,
  ) -> (Either<Edge<S>, State>, u32, Self) {
    let mut tape = Self::new();
    let (new_state, num_steps) = tape.simulate(machine, START, num_steps);
    (new_state, num_steps, tape)
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct ExpTape<S> {
  left: Vec<(S, u32)>,
  head: S,
  right: Vec<(S, u32)>,
}

impl<S: TapeSymbol> ExpTape<S> {
  fn new() -> Self {
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
  fn step(&mut self, state: State, t: &impl Turing<S>) -> Either<Edge<S>, State> {
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
      // dbg!(&self, state);
    }
    (Right(state), num_steps)
  }

  fn simulate_from_start(
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

  fn to_tape(ExpTape { left, head, right }: &ExpTape<S>) -> Tape<S> {
    Tape {
      left: Self::splat(left),
      head: *head,
      right: Self::splat(right),
    }
  }
}

pub fn tnf_simulate(inp_machine: SmallBinMachine, total_steps: u32) -> Vec<SmallBinMachine> {
  let mut out = vec![];

  struct TnfState {
    machine: SmallBinMachine,
    state: State,
    tape: Tape<bool>,
    num_steps: u32,
  }

  let mut stack = vec![TnfState {
    machine: inp_machine,
    state: START,
    tape: Tape::new(),
    num_steps: 0,
  }];
  while let Some(TnfState {
    machine,
    state,
    mut tape,
    num_steps,
  }) = stack.pop()
  {
    match tape.simulate(&machine, state, total_steps - num_steps) {
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
  use crate::turing::{get_machine, HALT};

  #[test]
  fn exptape_to_tape() {
    let e_tape = ExpTape {
      left: vec![(true, 2), (false, 1)],
      head: false,
      right: vec![(true, 1), (false, 3), (true, 1)],
    };
    let tape = Tape {
      left: vec![true, true, false],
      head: false,
      right: vec![true, false, false, false, true],
    };
    assert_eq!(ExpTape::to_tape(&e_tape), tape)
  }
  #[test]
  fn sim_bb2() {
    let bb2 = get_machine("bb2");
    let (state, num_steps, tape) = Tape::simulate_from_start(&bb2, 10);
    dbg!(&tape);
    assert_eq!(state, Right(HALT));
    assert_eq!(num_steps, 6);
    assert_eq!(
      tape,
      Tape {
        left: vec![true, true],
        head: true,
        right: vec![true]
      }
    );
    let (e_state, e_steps, e_tape) = ExpTape::simulate_from_start(&bb2, 10);
    assert_eq!(
      (e_state, e_steps, ExpTape::to_tape(&e_tape)),
      (state, num_steps, tape)
    );
  }
  #[test]
  fn sim_bb3() {
    let bb3 = get_machine("bb3");
    let (state, num_steps, tape) = Tape::simulate_from_start(&bb3, 30);
    dbg!(&tape);
    assert_eq!(state, Right(HALT));
    assert_eq!(num_steps, 14);
    assert_eq!(
      tape,
      Tape {
        left: vec![true, true, true],
        head: true,
        right: vec![true, true]
      }
    );
    let (e_state, e_steps, e_tape) = ExpTape::simulate_from_start(&bb3, 30);
    assert_eq!(
      (e_state, e_steps, ExpTape::to_tape(&e_tape)),
      (state, num_steps, tape)
    );
  }
  //todo: simulate bb4 to further sanity check

  //tests to write: bb4, tnf_simulate
}
