#[allow(unused)]
use either::Either::{self, Left, Right};
use std::{fmt::Debug, vec};

use crate::turing::{Dir, Trans, Turing};

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
#[derive(Debug, PartialEq, Eq, Hash)]
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
  // return either final state (Right) or the input state+var that the machine couldn't handle (Left)
  fn step(&mut self, state: u8, t: &impl Turing<S>) -> Either<(u8, S), u8> {
    let Trans { state, symbol, dir } = match t.step(state, self.head) {
      Some(trans) => trans,
      None => return Left((state, self.head)),
    };
    self.head = symbol;
    self.move_dir(dir);
    Right(state)
  }

  fn simulate(
    &mut self,
    machine: &impl Turing<S>,
    mut state: u8,
    num_steps: u32,
  ) -> (Either<(u8, S), u8>, u32) {
    /* return:
    0: from step
    1: the number of steps executed
     */
    for step in 1..num_steps + 1 {
      state = match self.step(state, machine) {
        Left((state, head)) => return (Left((state, head)), step),
        Right(0) => return (Right(0), step),
        Right(state) => state,
      };
      // dbg!(&self, state);
    }
    (Right(state), num_steps)
  }

  fn simulate_from_start(
    machine: &impl Turing<S>,
    num_steps: u32,
  ) -> (Either<(u8, S), u8>, u32, Tape<S>) {
    let mut tape = Self::new();
    let (new_state, num_steps) = tape.simulate(machine, 1, num_steps);
    (new_state, num_steps, tape)
  }
}

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

  fn step(&mut self, state: u8, t: &impl Turing<S>) -> Either<(u8, S), u8> {
    let Trans { state, symbol, dir } = match t.step(state, self.head) {
      Some(trans) => trans,
      None => return Left((state, self.head)),
    };
    self.head = symbol;
    self.move_dir(dir);
    Right(state)
  }
}

mod test {
  use super::*;
  use crate::turing::get_machine;

  #[test]
  fn sim_bb2() {
    let bb2 = get_machine("bb2");
    let (new_state, num_steps, tape) = Tape::simulate_from_start(&bb2, 10);
    dbg!(&tape);
    assert_eq!(new_state, Right(0));
    assert_eq!(num_steps, 6);
    assert_eq!(
      tape,
      Tape {
        left: vec![true, true],
        head: true,
        right: vec![true]
      }
    )
  }
  #[test]
  fn sim_bb3() {
    let bb3 = get_machine("bb3");
    let (new_state, num_steps, tape) = Tape::simulate_from_start(&bb3, 30);
    dbg!(&tape);
    assert_eq!(new_state, Right(0));
    assert_eq!(num_steps, 14);
    assert_eq!(
      tape,
      Tape {
        left: vec![true, true, true],
        head: true,
        right: vec![true, true]
      }
    );
  }
  //todo: simulate bb4 to further sanity check
}
