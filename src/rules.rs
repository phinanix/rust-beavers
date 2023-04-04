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

use crate::{
  simulate::TapeSymbol,
  turing::{Edge, State, Trans, Turing},
};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Config<S> {
  state: State,
  left: Vec<(S, u32)>,
  head: S,
  right: Vec<(S, u32)>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Rule<S> {
  start: Config<S>,
  end: Config<S>,
}

pub fn detect_chain_rules<S: TapeSymbol>(machine: &impl Turing<S>) -> Vec<Rule<S>> {
  /* whenever there is a transition XS -> XTD for state X, symbols S,T, dir D
    there is a chain rule (X, >S< S^n) -> (X, T^n >T<) (shown here for R).
  */
  let mut out = vec![];
  for state_in in machine.all_states() {
    for symbol_in in S::all_symbols() {
      let Trans {state: state_out, symbol: symbol_out, dir} = 
        machine.step(Edge(state_in, symbol_in)).expect("machine is defined");
    }
  }
  out
}
