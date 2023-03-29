#[allow(unused)]

use smallvec::{SmallVec, smallvec};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dir {L, R}
use Dir::*;

// by convention, state 0 is halting. you can theoretically do anything when you halt but the
// convention is to go R and write a 1. 
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Trans<S> {
  pub state: u8, pub symbol: S, pub dir: Dir
}

const AB: &str = "ZABCDEFG";

impl Trans<bool> {
  fn from_compact_format(inp: &str) -> Option<Self> {
    match inp.as_bytes() {
      &[symbol, dir, state] => {
        if (symbol as char) == '-' {
          assert_eq!(dir as char, '-');
          assert_eq!(state as char, '-');
          return None;
        }
        let symbol = match symbol as char {
          '0' => false,
          '1' => true,
          _ => panic!("{} is not a valid symbol", symbol)
        };
        let dir = match dir as char {
          'L' => L, 
          'R' => R, 
          _ => panic!("{} is not a valid direction", dir),
        };
        //Z is 0 for halt, and then A is 1 and so on
        let state: u8 = AB.find(state as char).expect("state was not a letter").try_into().unwrap();
        return Some(Trans{state, symbol, dir});
      }, 
      _ => panic!("{} is not a valid trans", inp),
    }
  }

  fn to_compact_format(&self) -> String {
    match self {
      &Trans { state, symbol, dir } => {
        let symbol_chr = if symbol {'1'} else {'0'};
        //todo factor this into dir
        let dir_chr = if dir==L {'L'} else {'R'};
        let state_chr = AB.chars().nth(state as usize).unwrap();

        let mut out = String::new();
        out.push(symbol_chr);
        out.push(dir_chr);
        out.push(state_chr);
        out
      },
    }
  }

}
// S = symbol
pub trait Turing<S> {
  fn step(&self, state: u8, symbol: S) -> Option<Trans<S>>;
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SmallBinMachine{num_states: u8, table: SmallVec<[Option<Trans<bool>>; 14]>}

impl Turing<bool> for SmallBinMachine {
  fn step(&self, state: u8, symbol: bool) -> Option<Trans<bool>> {
    assert_ne!(state, 0); // you can't make progress from a halt state
    let state = state - 1; // the table has no entries for halting states ofc
    assert!(state < self.num_states);
    *self.table.get((state*2 + if symbol {1} else {0}) as usize).unwrap()
  }
}

impl SmallBinMachine {
  fn from_compact_format(inp: &str) -> Self {
    // example compact format
    // 1RB0RD_1LB1LC_1RC1LD_1RE0LD_1RA---
    // groups of 3 make a transition, underscores between pairs, triple --- for undefined
    assert_eq!(inp.len() % 7, 6);
    let num_states : usize = (inp.len() + 1) / 7;
    let mut table = smallvec![];
    for state in 0..num_states {
      let index = state * 7;
      table.push(Trans::from_compact_format(&inp[index..index+3]));
      table.push(Trans::from_compact_format(&inp[index+3..index+6]));
    }
    Self{num_states: num_states.try_into().unwrap(), table}
  }

  fn to_compact_format(&self) -> String {
    let mut out = String::new();
    for (i, &trans) in self.table.iter().enumerate() {
      match trans {
        None => out.push_str("---"),
        Some(trans) => out.push_str(&trans.to_compact_format()),
      }
      if i % 2 == 1 && i+1 != (self.num_states*2).into() {
        out.push('_');
      }
    }
    out
  }
}


mod test {
  use super::*;

  #[test]
  fn trans_from_string() {
    let trans = Trans {state: 3, dir: L, symbol: true};
    let trans_str = "1LC";
    assert_eq!(Some(trans), Trans::from_compact_format(trans_str));
    assert_eq!(trans_str, Trans::to_compact_format(&trans));
  }

  #[test]
  fn machine_from_string() {
    let machine_str = "1RB0RB_1LA---";
    let num_states = 2;
    let table = smallvec!
      [ Some(Trans{state: 2, dir: R, symbol: true})
      , Some(Trans{state: 2, dir: R, symbol: false})
      , Some(Trans{state: 1, dir: L, symbol: true})
      , None
      ];
    let machine = SmallBinMachine{num_states, table};
    assert_eq!(machine, SmallBinMachine::from_compact_format(&machine_str));
    assert_eq!(machine.to_compact_format(), machine_str)
  }

}