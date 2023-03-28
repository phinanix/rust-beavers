
use smallvec::{SmallVec};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Dir {L, R}
use Dir::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Trans<S> {
  state: u8, symbol: S, dir: Dir
}

// S = symbol
trait Turing<S> {
  fn step(&self, state: u8, symbol: S) -> Option<Trans<S>>;
}


struct SmallBinMachine{size: u8, table: SmallVec<[Option<Trans<bool>>; 14]>}

impl Turing<bool> for SmallBinMachine {
  fn step(&self, state: u8, symbol: bool) -> Option<Trans<bool>> {
    assert!(state < self.size);
    *self.table.get((state*2 + if symbol {1} else {0}) as usize).unwrap()
  }
}

impl SmallBinMachine {
  fn from_compact_format(inp: &str) -> Self {
    todo!()
  }
}


fn main() {
    println!("Hello, world!");
}
