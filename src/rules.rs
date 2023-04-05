/*
 idea, be able to discern the existence of + prove + use for acceleration a variety of "rules"
 discern existence:
  - notice "chain rules" automatically from the turing machine itself
  - make a simulator which tracks "signatures" and compares multiple occurences of the same signature
    to each other
    - first: guess linear difference
    - ~second: detect counters via 0^x 1^y -> 0^(x-1) 1^(y+1) (or via 1^a 0^b -> 1^(a+1) 0^(b-1) ?)

 prove: you have some kind of tape that you play forward ig
 use for acceleration: you play forward the rule on the normal tape.
   of course the big "acceleration" is to accelerate to infinity, where you notice that a rule
   can be applied infinitey often.

 to decide: track how many steps rules take, or not yet? for a very first prototype no, but could
 implement it soon-ish in order to not get too behind.
*/

/*
 we need a struct that can handle both
 >S< S^n -> T^n >T<
 and
 0 1^n >0< -> 1^(n+1) >0<
*/

use std::collections::HashMap;

use smallvec::{smallvec, SmallVec};

use crate::turing::{
  Dir::{L, R},
  Edge, State, TapeSymbol, Trans, Turing,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Var(u8);

//ax + n
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct AffineVar {
  pub n: u32,
  pub a: u32,
  pub var: Var,
}

impl AffineVar {
  pub fn sub(&self, x: u32) -> u32 {
    let AffineVar { n, a, var: _var } = self;
    return n + a * x;
  }

  pub fn sub_map(&self, hm: &HashMap<Var, u32>) -> u32 {
    let &x = hm.get(&self.var).unwrap();
    self.sub(x)
  }
}

// much like Tape / ExpTape, the *last* thing in the Vec is the closest to the head,
// for both left and right
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Config<S> {
  pub state: State,
  pub left: Vec<(S, AffineVar)>,
  pub head: S,
  pub right: Vec<(S, AffineVar)>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Rule<S> {
  pub start: Config<S>,
  pub end: Config<S>,
}

impl<S: TapeSymbol> Rule<S> {
  pub fn start_edge_index(&self) -> usize {
    match self {
      Rule {
        start:
          Config {
            state,
            left: _left,
            head,
            right: _right,
          },
        end: _end,
      } => return Edge(*state, *head).edge_index(),
    }
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Rulebook<S>(u8, SmallVec<[Vec<Rule<S>>; 14]>);

impl<S: TapeSymbol> Rulebook<S> {
  pub fn new(num_states: u8) -> Self {
    let mut sv = smallvec![];
    for _ in 0..2 * num_states {
      sv.push(vec![]);
    }
    Self(num_states, sv)
  }

  pub fn add_rule(&mut self, rule: Rule<S>) {
    self.1[rule.start_edge_index()].push(rule);
  }

  pub fn get_rules(&self, edge: Edge<S>) -> &Vec<Rule<S>> {
    &self.1[edge.edge_index()]
  }
}

pub fn detect_chain_rules<S: TapeSymbol>(machine: &impl Turing<S>) -> Vec<Rule<S>> {
  /* whenever there is a transition XS -> XTD for state X, symbols S,T, dir D
    there is a chain rule (X, >S< S^n) -> (X, T^n >T<) (shown here for R).
  */
  let mut out = vec![];
  for state_in in machine.all_states() {
    for symbol_in in S::all_symbols() {
      let Trans {
        state: state_out,
        symbol: symbol_out,
        dir,
      } = machine
        .step(Edge(state_in, symbol_in))
        .expect("machine is defined");
      if state_in == state_out {
        let sym_var = AffineVar {
          n: 0,
          a: 1,
          var: Var(0),
        };
        let half_tape_in = vec![(symbol_in, sym_var)];
        let half_tape_out = vec![(symbol_out, sym_var)];
        match dir {
          L => {
            let start = Config {
              state: state_in,
              left: half_tape_in,
              head: symbol_in,
              right: vec![],
            };
            let end = Config {
              state: state_in,
              left: vec![],
              head: symbol_out,
              right: half_tape_out,
            };
            out.push(Rule { start, end });
          }
          R => {
            let start = Config {
              state: state_in,
              left: vec![],
              head: symbol_in,
              right: half_tape_in,
            };
            let end = Config {
              state: state_in,
              left: half_tape_out,
              head: symbol_out,
              right: vec![],
            };
            out.push(Rule { start, end });
          }
        }
      }
    }
  }
  out
}

mod test {
  use super::*;
  // affinevar: sub, submap
  // detect chain rules
}
