use itertools::Itertools;
#[allow(unused)]
use smallvec::{smallvec, SmallVec};
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Write};
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Bit(pub bool);
impl Display for Bit {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      &Bit(true) => f.write_char('T'),
      &Bit(false) => f.write_char('F'),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Dir {
  L,
  R,
}
use Dir::*;

impl Dir {
  pub fn flip(&self) -> Self {
    match self {
      L => R,
      R => L,
    }
  }
  pub fn to_displacement(&self) -> i32 {
    match self {
      L => -1,
      R => 1,
    }
  }
}

impl Display for Dir {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      L => write!(f, "L"),
      R => write!(f, "R"),
    }
  }
}

pub trait Phase: Clone + Copy + PartialEq + Eq + Hash + Debug + Display {
  fn halted(self: Self) -> bool;
  const START: Self;
  const INFINITE: Self;
  // laws: never returns 0; is 1-1
  fn as_byte(self: Self) -> u8;
}

// the state a machine is in. 0 is Halt
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct State(pub u8);

// pub const START: State = State(1);
// pub const INFINITE: State = State(255);

pub const HALT: State = State(0);

impl Phase for State {
  fn halted(self: Self) -> bool {
    self == State(0)
  }
  const START: Self = State(1);
  const INFINITE: Self = State(255);
  fn as_byte(self: Self) -> u8 {
    self.0
  }
}

impl Display for State {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      &HALT => f.write_str("HALT"),
      &State(i) => f.write_char(AB.chars().nth(i as usize).unwrap()),
    }
  }
}

pub trait TapeSymbol: Copy + Eq + Hash + Debug + Display {
  fn empty() -> Self;
  fn all_symbols() -> Vec<Self>;
  fn num_symbols() -> usize {
    Self::all_symbols().len()
  }
}

impl TapeSymbol for Bit {
  fn empty() -> Self {
    Bit(false)
  }

  fn all_symbols() -> Vec<Self> {
    vec![Bit(false), Bit(true)]
  }
}

// the input to a TM's transition function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Edge<P, S>(pub P, pub S);

impl<P: Phase, S: TapeSymbol> Edge<P, S> {
  pub fn edge_index(&self) -> usize {
    let &Self(phase, symbol) = self;
    //index by state, then by symbol, so output is state*num_symbols + index_symbol
    let symbols = S::all_symbols();
    let num_symbols = S::num_symbols();
    let symbol_index = symbols.into_iter().position(|s| s == symbol).unwrap();
    return (phase.as_byte() - 1) as usize * num_symbols + symbol_index;
  }

  pub fn num_edges(num_states: u8) -> usize {
    let num_symbols = S::num_symbols();
    num_symbols * usize::from(num_states)
  }
}

// the output of a TM's transition function
// by convention, state 0 is halting. you can theoretically do anything when you halt but the
// convention is to go R and write a 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Trans<P, S> {
  Step {
    state: P,
    symbol: S,
    dir: Dir,
    steps: u32,
  },
  Halt {
    state: P,
    symbol: S,
    mb_dir: Option<Dir>,
    steps: u32,
  },
  Infinite,
}
use Trans::*;

pub const HALT_TRANS: Trans<State, Bit> = Halt {
  state: HALT,
  symbol: Bit(true),
  mb_dir: Some(R),
  steps: 1,
};

pub const AB: &str = "HABCDEFG";

impl Trans<State, Bit> {
  fn possible_trans(max_state: u8) -> Vec<Self> {
    let mut out = vec![HALT_TRANS];
    for state in 1..=max_state {
      for symbol in Bit::all_symbols() {
        for dir in [L, R] {
          out.push(Step { state: State(state), symbol, dir, steps: 1 })
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
          '0' => Bit(false),
          '1' => Bit(true),
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
        if state == 0 {
          return Some(Halt { state: HALT, symbol, mb_dir: Some(dir), steps: 1 });
        }
        return Some(Step { state: State(state), symbol, dir, steps: 1 });
      }
      _ => panic!("{} is not a valid trans", inp),
    }
  }

  fn to_compact_format(&self) -> String {
    match self {
      &Step {
        state: State(state),
        symbol: Bit(symbol),
        dir,
        steps: _,
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

      &Halt {
        state: HALT,
        symbol: Bit(symbol),
        mb_dir: Some(dir),
        steps: _,
      } => {
        let symbol_chr = if symbol { '1' } else { '0' };
        //todo factor this into dir
        let dir_chr = if dir == L { 'L' } else { 'R' };
        let state_chr = 'H';
        let mut out = String::new();
        out.push(symbol_chr);
        out.push(dir_chr);
        out.push(state_chr);
        out
      }
      &Halt { state: not_halt, symbol: _, mb_dir: _, steps: _ } => {
        unreachable!("halt with not halt {}", not_halt)
      }
      &Infinite => unreachable!("SmallBinMachine has no infinite trans"),
    }
  }
}
// S = symbol
// P = phase (aka state, but that is overloaded)
pub trait Turing<P, S> {
  fn all_states(&self) -> Vec<P>;
  fn num_states(&self) -> u8 {
    self.all_states().len() as u8
  }
  fn step(&self, edge: Edge<P, S>) -> Option<Trans<P, S>>;
  fn to_compact_format(&self) -> String;
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmallBinMachine {
  num_states: u8,
  table: SmallVec<[Option<Trans<State, Bit>>; 14]>,
}

impl Turing<State, Bit> for SmallBinMachine {
  fn all_states(&self) -> Vec<State> {
    (1..=self.num_states)
      .into_iter()
      .map(|i| State(i))
      .collect()
  }

  fn num_states(&self) -> u8 {
    self.num_states
  }

  fn step(&self, edge: Edge<State, Bit>) -> Option<Trans<State, Bit>> {
    *self.table.get(self.edge_index(edge)).unwrap()
  }

  fn to_compact_format(&self) -> String {
    self.to_compact_format()
  }
}

impl SmallBinMachine {
  fn edge_index(&self, Edge(State(state), Bit(symbol)): Edge<State, Bit>) -> usize {
    assert_ne!(state, 0); // you can't make progress from a halt state
    let state = state - 1; // the table has no entries for halting states ofc
    assert!(state < self.num_states, "{}", self.to_compact_format());
    (state * 2 + if symbol { 1 } else { 0 }) as usize
  }

  pub fn start_machine(num_states: u8, first_write: Bit) -> Self {
    let trans = Step {
      state: State(2),
      symbol: first_write,
      dir: R,
      steps: 1,
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

  pub fn define_trans_in_machine(
    &self,
    edge_index: usize,
    new_transitions: &[Trans<State, Bit>],
  ) -> Vec<Self> {
    let mut out = vec![];
    for &trans in new_transitions {
      let mut new_machine = self.clone();
      new_machine.table[edge_index] = Some(trans);
      out.push(new_machine);
    }
    out
  }

  pub fn branch_on_edge(&self, edge: Edge<State, Bit>, allow_no_halt: bool) -> Vec<Self> {
    let edge_index = self.edge_index(edge);
    assert_eq!(self.table[edge_index], None);

    if self.num_undefined_trans() == 1 && !allow_no_halt {
      let mut cloned = self.clone();
      cloned.table[edge_index] = Some(HALT_TRANS);
      return vec![cloned];
    }

    let mut to_print = false;
    let max_state_index = match self.first_undefined_state() {
      Some(undef_state) => {
        // first undefined state is 0-indexed, but State (the type) is 1-indexed,
        // so this conversion converts from 0-indexing to 1-indexing
        let ans = undef_state + 1;
        // if the transition we're defining is in a state which has no transitions
        // defined yet ------, then we are allowed to go to the *next higher* state
        if ans == edge.0 .0 && ans < self.num_states {
          // panic!("{:?} {}", edge, self.to_compact_format());
          ans + 1
        } else {
          ans
        }
      }
      None => self.num_states,
    };

    let possible_trans = Trans::possible_trans(max_state_index);
    if possible_trans.len() < 13 {
      to_print = true
    };
    if to_print {
      dbg!(max_state_index, self.first_undefined_state());
      dbg!(self.to_compact_format(), edge, edge_index);
      dbg!(possible_trans.len(), &possible_trans);
      println!();
    }
    self.define_trans_in_machine(edge_index, &possible_trans)
  }

  pub fn remove_unused_states(mut self) -> Self {
    let mut used_states = HashSet::new();
    used_states.insert(State::START);
    for trans in self.table.iter() {
      match trans {
        Some(Step { state, symbol: _, dir: _, steps: _ }) => {
          used_states.insert(*state);
        }
        _ => (),
      }
    }
    let unused_states = self
      .all_states()
      .into_iter()
      .filter(|s| !used_states.contains(s))
      .collect_vec();
    for used_state in used_states.iter() {
      for unused_state in unused_states.iter() {
        assert!(
          used_state.0 < unused_state.0,
          "{:?} vs {:?}",
          &used_states,
          &unused_states
        );
      }
    }

    self.num_states = used_states.len().try_into().unwrap();
    for _ in 0..(unused_states.len() * 2) {
      self.table.pop();
    }
    assert_eq!(self.table.len(), (self.num_states * 2).into());
    self
  }

  pub fn determinize_machine(&self) -> Vec<Self> {
    // let mut out = vec![self.clone()];
    let base_machine = self.clone().remove_unused_states();
    if base_machine.num_undefined_trans() == 0 {
      return vec![base_machine];
    }
    let undefined_trans: SmallVec<[usize; 6]> = base_machine
      .table
      .iter()
      .enumerate()
      .filter_map(|(i, mb_trans)| if mb_trans.is_none() { Some(i) } else { None })
      .collect();
    // we have to pick 1 trans to be halt, and the rest are not halt
    let mut out = vec![];
    for &trans_selected_to_halt in undefined_trans.iter() {
      let mut new_machine = base_machine.clone();
      new_machine.table[trans_selected_to_halt] = Some(HALT_TRANS);
      out.push(new_machine);
    }

    let possible_trans = Trans::possible_trans(self.num_states);
    // the other transitions we won't make halt, so this relies on how Trans::possible_trans
    // returns HALT_TRANS at the head of the vector
    assert_eq!(possible_trans[0], HALT_TRANS);

    for trans_to_define in undefined_trans {
      out = out
        .into_iter()
        .flat_map(|m| {
          if m.table[trans_to_define].is_some() {
            vec![m]
          } else {
            m.define_trans_in_machine(trans_to_define, &possible_trans[1..])
          }
        })
        .collect();
    }
    return out;
  }

  pub fn has_halt_trans(&self) -> bool {
    self
      .table
      .iter()
      .any(|&mb_trans| mb_trans == Some(HALT_TRANS))
  }

  pub fn from_compact_format(inp: &str) -> Self {
    // example compact format
    // 1RB0RD_1LB1LC_1RC1LD_1RE0LD_1RA---
    // groups of 3 make a transition, underscores between pairs, triple --- for undefined
    assert_eq!(inp.len() % 7, 6, "{} not right len", inp);
    let num_states: usize = (inp.len() + 1) / 7;
    let mut table = smallvec![];
    for state in 0..num_states {
      let index = state * 7;
      table.push(Trans::from_compact_format(&inp[index..index + 3]));
      table.push(Trans::from_compact_format(&inp[index + 3..index + 6]));
    }
    Self { num_states: num_states.try_into().unwrap(), table }
  }

  pub fn to_compact_format(&self) -> String {
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

#[cfg(test)]
mod test {
  use itertools::Itertools;

  use super::*;

  #[test]
  fn trans_from_string() {
    let trans = Step {
      state: State(3),
      dir: L,
      symbol: Bit(true),
      steps: 1,
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
      Some(Step {
        state: State(2),
        dir: R,
        symbol: Bit(true),
        steps: 1
      }),
      Some(Step {
        state: State(2),
        dir: R,
        symbol: Bit(false),
        steps: 1
      }),
      Some(Step {
        state: State(1),
        dir: L,
        symbol: Bit(true),
        steps: 1
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
    let mut ans: Vec<Trans<State, Bit>> = vec![
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
    let branched_machines = machine.branch_on_edge(Edge(State(2), Bit(true)), false);
    assert_eq!(
      branched_machines,
      vec![SmallBinMachine::from_compact_format("1RB0RB_1LA1RH")]
    );

    let machine_str = "1LA---_------";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let mut branched_machines = machine.branch_on_edge(Edge(State(1), Bit(true)), false);
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

  #[test]
  fn test_remove_unused() {
    let machine = SmallBinMachine::from_compact_format("1RB0RB_1LA---");
    let rem_unused_machine = machine.clone().remove_unused_states();
    assert_eq!(machine, rem_unused_machine);

    let machine = SmallBinMachine::from_compact_format("1RB0LB_1LA0RA_------");
    let rem_unused_machine = machine.clone().remove_unused_states();
    let ans_machine = SmallBinMachine::from_compact_format("1RB0LB_1LA0RA");
    assert_eq!(ans_machine, rem_unused_machine);
  }

  #[test]
  fn determinize_test() {
    let machine_str = "1RB0RB_1LA---";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let det_machine = SmallBinMachine::from_compact_format("1RB0RB_1LA1RH");
    let det_vec = machine.determinize_machine();
    assert_eq!(
      det_vec.clone(),
      vec![det_machine.clone()],
      "ans: [{}] actual res: {}",
      det_machine.to_compact_format(),
      det_vec
        .into_iter()
        .map(|m| m.to_compact_format())
        .join("\n")
    );

    let machine_str = "1RB0RB_------";
    let machine = SmallBinMachine::from_compact_format(machine_str);
    let det_machine_strs = vec![
      "1RB0RB_0LA1RH",
      "1RB0RB_0LB1RH",
      "1RB0RB_0RA1RH",
      "1RB0RB_0RB1RH",
      "1RB0RB_1LA1RH",
      "1RB0RB_1LB1RH",
      "1RB0RB_1RA1RH",
      "1RB0RB_1RB1RH",
      "1RB0RB_1RH0LA",
      "1RB0RB_1RH0LB",
      "1RB0RB_1RH0RA",
      "1RB0RB_1RH0RB",
      "1RB0RB_1RH1LA",
      "1RB0RB_1RH1LB",
      "1RB0RB_1RH1RA",
      "1RB0RB_1RH1RB",
    ];
    let mut det_machines = det_machine_strs
      .clone()
      .into_iter()
      .map(|s| SmallBinMachine::from_compact_format(s))
      .collect_vec();
    let mut det_vec = machine.determinize_machine();
    det_machines.sort();
    det_vec.sort();
    assert_eq!(
      det_vec.clone(),
      det_machines,
      "ans: [{}] actual res: {}",
      det_machine_strs.join("\n"),
      det_vec
        .into_iter()
        .map(|m| m.to_compact_format())
        .join("\n")
    );
  }
}
