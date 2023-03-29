
use core::num;

use crate::turing::{Turing, Trans, Dir};

// tape has two stacks and a symbol the machine is currently reading
// since these are array-backed vectors, the "front" is actually at the end
// and the "front" for both the left and the right, is the part which is 
// closest to the machine head
// so the turing tape 100 >1< 1110 would be 
// vec![1, 0, 0] 1 vec![0, 1, 1, 1] 
// the infinite stack of empty symbols is represented implicitly 
struct Tape<S> {
  left: Vec<S>, head: S, right: Vec<S>
}

trait TapeSymbol: Copy + Eq {
  fn empty() -> Self;
}


impl<S:TapeSymbol> Tape<S> {
  fn new() -> Self {
    Tape { left: vec![], head: TapeSymbol::empty(), right: vec![] }
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
  fn step(&mut self, state: u8, t: &impl Turing<S>) -> Option<u8> {
    let Trans{state, symbol, dir} = t.step(state, self.head)?; 
    self.head = symbol; 
    self.move_dir(dir);
    Some(state)
  }

}

fn simulate<S: TapeSymbol>(machine: &impl Turing<S>, tape: &mut Tape<S>, mut state: u8, num_steps: u32) -> u8 {
  for step in 0..num_steps {
    let state = tape.step(state, machine); 
  }
  state
}