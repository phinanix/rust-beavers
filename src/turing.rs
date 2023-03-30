use smallvec::{smallvec, SmallVec};
#[allow(unused)]
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Dir {
  L,
  R,
}
use Dir::*;

// the state a machine is in. 0 is Halt
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct State(pub u8);

pub const HALT: State = State(0);
pub const START: State = State(1);

// the input to a TM's transition function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Edge<S>(pub State, pub S);

// the output of a TM's transition function
// by convention, state 0 is halting. you can theoretically do anything when you halt but the
// convention is to go R and write a 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Trans<S> {
  pub state: State,
  pub symbol: S,
  pub dir: Dir,
}

pub const HALT_TRANS: Trans<bool> = Trans {
  state: HALT,
  symbol: true,
  dir: R,
};

const AB: &str = "HABCDEFG";

impl Trans<bool> {
  fn possible_trans(max_state: u8) -> Vec<Self> {
    let mut out = vec![HALT_TRANS];
    for state in 1..=max_state {
      for symbol in [false, true] {
        for dir in [L, R] {
          out.push(Trans {
            state: State(state),
            symbol,
            dir,
          })
        }
      }
    }
    out
  }

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
          _ => panic!("{} is not a valid symbol", symbol),
        };
        let dir = match dir as char {
          'L' => L,
          'R' => R,
          _ => panic!("{} is not a valid direction", dir),
        };
        //H is 0 for halt, and then A is 1 and so on
        let state: u8 = AB
          .find(state as char)
          .expect("state was not a letter")
          .try_into()
          .unwrap();
        return Some(Trans {
          state: State(state),
          symbol,
          dir,
        });
      }
      _ => panic!("{} is not a valid trans", inp),
    }
  }

  fn to_compact_format(&self) -> String {
    match self {
      &Trans {
        state: State(state),
        symbol,
        dir,
      } => {
        let symbol_chr = if symbol { '1' } else { '0' };
        //todo factor this into dir
        let dir_chr = if dir == L { 'L' } else { 'R' };
        let state_chr = AB.chars().nth(state as usize).unwrap();

        let mut out = String::new();
        out.push(symbol_chr);
        out.push(dir_chr);
        out.push(state_chr);
        out
      }
    }
  }
}
// S = symbol
pub trait Turing<S> {
  fn step(&self, edge: Edge<S>) -> Option<Trans<S>>;
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmallBinMachine {
  num_states: u8,
  table: SmallVec<[Option<Trans<bool>>; 14]>,
}

impl Turing<bool> for SmallBinMachine {
  fn step(&self, edge: Edge<bool>) -> Option<Trans<bool>> {
    *self.table.get(self.edge_index(edge)).unwrap()
  }
}

impl SmallBinMachine {
  fn edge_index(&self, Edge(State(state), symbol): Edge<bool>) -> usize {
    assert_ne!(state, 0); // you can't make progress from a halt state
    let state = state - 1; // the table has no entries for halting states ofc
    assert!(state < self.num_states);
    (state * 2 + if symbol { 1 } else { 0 }) as usize
  }

  pub fn start_machine(num_states: u8, first_write: bool) -> Self {
    let trans = Trans {
      state: State(2),
      symbol: first_write,
      dir: R,
    };
    let mut table = smallvec![Some(trans)];
    for _ in 1..(num_states * 2) {
      table.push(None);
    }
    Self { num_states, table }
  }

  fn num_undefined_trans(&self) -> usize {
    self
      .table
      .iter()
      .filter(|mb_trans| mb_trans.is_none())
      .count()
  }

  fn state_is_undefined(&self, state: u8) -> bool {
    self.table[(2 * state) as usize] == None && self.table[(2 * state + 1) as usize] == None
  }

  fn first_undefined_state(&self) -> Option<u8> {
    let mut state = self.num_states - 1;
    if !self.state_is_undefined(state) {
      return None;
    };

    while self.state_is_undefined(state) {
      state -= 1;
    }
    Some(state + 1)
  }

  pub fn branch_on_edge(&self, edge: Edge<bool>) -> Vec<Self> {
    let edge_index = self.edge_index(edge);
    assert_eq!(self.table[edge_index], None);
    if self.num_undefined_trans() == 1 {
      let mut cloned = self.clone();
      cloned.table[edge_index] = Some(HALT_TRANS);
      return vec![cloned];
    }

    let mut out = vec![];

    let max_state_index = match self.first_undefined_state() {
      Some(undef_state) => undef_state,
      None => self.num_states - 1,
    };

    let possible_trans = Trans::possible_trans(max_state_index + 1);
    for trans in possible_trans {
      let mut new_machine = self.clone();
      new_machine.table[edge_index] = Some(trans);
      out.push(new_machine);
    }
    out
  }

  fn from_compact_format(inp: &str) -> Self {
    // example compact format
    // 1RB0RD_1LB1LC_1RC1LD_1RE0LD_1RA---
    // groups of 3 make a transition, underscores between pairs, triple --- for undefined
    assert_eq!(inp.len() % 7, 6);
    let num_states: usize = (inp.len() + 1) / 7;
    let mut table = smallvec![];
    for state in 0..num_states {
      let index = state * 7;
      table.push(Trans::from_compact_format(&inp[index..index + 3]));
      table.push(Trans::from_compact_format(&inp[index + 3..index + 6]));
    }
    Self {
      num_states: num_states.try_into().unwrap(),
      table,
    }
  }

  fn to_compact_format(&self) -> String {
    let mut out = String::new();
    for (i, &trans) in self.table.iter().enumerate() {
      match trans {
        None => out.push_str("---"),
        Some(trans) => out.push_str(&trans.to_compact_format()),
      }
      if i % 2 == 1 && i + 1 != (self.num_states * 2).into() {
        out.push('_');
      }
    }
    out
  }
}

const MACHINES: [(&str, &str); 3] = [
  ("bb2", "1RB1LB_1LA1RH"),
  ("bb3", "1RB1RH_0RC1RB_1LC1LA"),
  ("bb4", ""),
];

pub fn get_machine(name: &str) -> SmallBinMachine {
  let machine_map = HashMap::from(MACHINES);
  SmallBinMachine::from_compact_format(machine_map.get(name).unwrap())
}

mod test {
  use super::*;

  #[test]
  fn trans_from_string() {
    let trans = Trans {
      state: State(3),
      dir: L,
      symbol: true,
    };
    let trans_str = "1LC";
    assert_eq!(Some(trans), Trans::from_compact_format(trans_str));
    assert_eq!(trans_str, Trans::to_compact_format(&trans));
  }

  #[test]
  fn machine_from_string() {
    let machine_str = "1RB0RB_1LA---";
    let num_states = 2;
    let table = smallvec![
      Some(Trans {
        state: State(2),
        dir: R,
        symbol: true
      }),
      Some(Trans {
        state: State(2),
        dir: R,
        symbol: false
      }),
      Some(Trans {
        state: State(1),
        dir: L,
        symbol: true
      }),
      None
    ];
    let machine = SmallBinMachine { num_states, table };
    assert_eq!(machine, SmallBinMachine::from_compact_format(&machine_str));
    assert_eq!(machine.to_compact_format(), machine_str)
  }

  #[test]
  fn possible_trans() {
    let mut possible_trans = Trans::possible_trans(2);
    let mut ans: Vec<Trans<bool>> = vec![
      "1RH", "0LA", "0RA", "1LA", "1RA", "0LB", "0RB", "1LB", "1RB",
    ]
    .into_iter()
    .map(|s| Trans::from_compact_format(s).unwrap())
    .collect();
    possible_trans.sort();
    ans.sort();
    assert_eq!(possible_trans, ans);
  }

  #[test]
  fn undefined_states() {
    let machine_str = "1RB0RB_1LA---";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let num_undef = machine.num_undefined_trans();
    let first_undef = machine.first_undefined_state();
    assert_eq!(num_undef, 1);
    assert_eq!(first_undef, None);

    let machine_str = "1RB0RB_1LA---_------";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let num_undef = machine.num_undefined_trans();
    let first_undef = machine.first_undefined_state();
    assert_eq!(num_undef, 3);
    assert_eq!(first_undef, Some(2));

    let machine_str = "1RB0RB_1LA---_------_------_------";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let num_undef = machine.num_undefined_trans();
    let first_undef = machine.first_undefined_state();
    assert_eq!(num_undef, 7);
    assert_eq!(first_undef, Some(2));

    let machine_str = "1RB0RB_1LA---_0RB---";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let num_undef = machine.num_undefined_trans();
    let first_undef = machine.first_undefined_state();
    assert_eq!(num_undef, 2);
    assert_eq!(first_undef, None);
  }

  #[test]
  fn branch_test() {
    let machine_str = "1RB0RB_1LA---";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let branched_machines = machine.branch_on_edge(Edge(State(2), true));
    assert_eq!(
      branched_machines,
      vec![SmallBinMachine::from_compact_format("1RB0RB_1LA1RH")]
    );

    let machine_str = "1LA---_------";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let mut branched_machines = machine.branch_on_edge(Edge(State(1), true));
    let mut branched_machines_str: Vec<String> = branched_machines
      .iter()
      .map(|m| SmallBinMachine::to_compact_format(&m))
      .collect();
    let mut ans_str = vec![
      "1LA1RH_------",
      "1LA1LA_------",
      "1LA1LB_------",
      "1LA1RA_------",
      "1LA1RB_------",
      "1LA0LA_------",
      "1LA0LB_------",
      "1LA0RA_------",
      "1LA0RB_------",
    ];
    branched_machines_str.sort();
    ans_str.sort();
    assert_eq!(branched_machines_str, ans_str);

    let mut ans: Vec<SmallBinMachine> = ans_str
      .into_iter()
      .map(|s| SmallBinMachine::from_compact_format(s))
      .collect();

    branched_machines.sort();
    ans.sort();
    assert_eq!(branched_machines, ans);
  }
}
