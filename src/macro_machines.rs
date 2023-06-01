/*
a program which takes a machine that uses a symbol and a number n and converts it to an equivalent
machine that treats n symbols of the base machine as 1 symbol of the higher ("macro") machine

n symbols of a given type S are represented as [S; n], possibly wrapped in a newtype so as to
support impl TapeSymbol

the key function a Turing machine needs to implement is step, which takes an
edge (State, S) and returns a Trans (State, S, Dir) (modulo machines being undefined, which I think
we ignore in this module)

A macro machine encodes in its state whether it is on the left or right side of the current symbol
So given a State and symbol pair, we need to simulate the machine until it loops (and then do what?)
or falls off either the left or right of the multi-symbol, at which point that is the direction,
and the new state and new symbol are obtainable

a State is a u8 right now, so we need a way to convert a higher state to a lower state

other tricky things:
1) what happens when the machine halts?
2) how do we count the base machine's steps?
3) how do we signal to the outer program that the machine runs forever?
 */

use std::collections::HashMap;

use itertools::{repeat_n, Itertools};

use crate::{
  tape::{ExpTape, StepResult::*},
  turing::{Dir, SmallBinMachine, State, TapeSymbol, Turing, HALT},
};

fn state_dir_to_macro_state(state: State, dir: Dir) -> State {
  todo!()
}

fn macro_state_to_state_dir(state: State) -> (State, Dir) {
  todo!()
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct MacroSymbol<S, const N: usize>(pub [S; N]);

impl<S: TapeSymbol, const N: usize> MacroSymbol<S, N> {
  pub fn all_symbols() -> Vec<Self> {
    repeat_n(S::all_symbols(), N)
      .multi_cartesian_product()
      .map(|s_vec| MacroSymbol(s_vec.try_into().unwrap()))
      .collect_vec()
  }

  pub fn from_tape(
    ExpTape { mut left, head, mut right, tape_end_inf }: ExpTape<S, u32>,
    dir: Dir,
  ) -> Self {
    assert!(!tape_end_inf);
    //panics if the tape is the wrong size
    match dir {
      Dir::L => {
        assert_eq!(left.len(), 0);
        ExpTape::push_rle(&mut right, head, false);
        Self(ExpTape::splat(&mut right.iter().rev()).try_into().unwrap())
      }
      Dir::R => {
        assert_eq!(right.len(), 0);
        ExpTape::push_rle(&mut left, head, false);
        Self(ExpTape::splat(&mut left.iter()).try_into().unwrap())
      }
    }
  }
}

pub struct MacroMachine<S, const N: usize>(
  HashMap<(State, Dir, MacroSymbol<S, N>), (State, Dir, MacroSymbol<S, N>, u32)>,
);

impl<S: TapeSymbol, const N: usize> MacroMachine<S, N> {
  pub fn new(machine: &impl Turing<S>) -> Self {
    let mut hm = HashMap::new();
    for state in machine.all_states() {
      for dir in [Dir::L, Dir::R] {
        for macro_symbol in MacroSymbol::all_symbols() {
          let ans = Self::calculate_macro_step(machine, state, dir, macro_symbol);
          hm.insert((state, dir, macro_symbol), ans);
        }
      }
    }
    Self(hm)
  }

  fn make_tape(dir: Dir, MacroSymbol(arr): MacroSymbol<S, N>) -> ExpTape<S, u32> {
    match dir {
      Dir::L => {
        let head = arr[0];
        let mut right = vec![];
        for &sym in arr[1..].into_iter().rev() {
          ExpTape::push_rle(&mut right, sym, false);
        }
        ExpTape { left: vec![], head, right, tape_end_inf: false }
      }
      Dir::R => {
        let head = arr[arr.len() - 1];
        let mut left = vec![];
        for &sym in &arr[0..arr.len() - 1] {
          ExpTape::push_rle(&mut left, sym, false)
        }
        ExpTape { left, head, right: vec![], tape_end_inf: false }
      }
    }
  }

  pub fn calculate_macro_step(
    machine: &impl Turing<S>,
    mut state: State,
    dir: Dir,
    sym: MacroSymbol<S, N>,
  ) -> (State, Dir, MacroSymbol<S, N>, u32) {
    // 1) make the tape for the machine to run on
    let mut tape = Self::make_tape(dir, sym);
    // 2) calculate the step limit
    let step_limit: usize =
      usize::from(machine.num_states()) * S::num_symbols().pow(N.try_into().unwrap()) * N;
    // 3) simulate up to that step limit, with 1 of 4 results:
    // a) machine loops b) machine halts c) machine falls off a side d) edge is undefined
    for step in 1..=step_limit {
      state = match tape.step_extra_info(state, machine) {
        UndefinedEdge(_) => todo!(), // d
        FellOffTape(state, d) => {
          return (
            state,
            d,
            MacroSymbol::from_tape(tape, d),
            step.try_into().unwrap(),
          ); // c
        }
        Success(state, _) => state,
      };
      if state == HALT {
        todo!(); // b
      }
    }
    todo!() // a
  }

  pub fn macro_step(
    &self,
    state: State,
    dir: Dir,
    sym: MacroSymbol<S, N>,
  ) -> (State, Dir, MacroSymbol<S, N>, u32) {
    let mb_ans = self.0.get(&(state, dir, sym));
    *mb_ans.unwrap()
  }
}

#[cfg(test)]
mod test {
  use crate::{
    parse::{parse_exact, parse_tape},
    turing::Bit,
  };

  use super::*;

  #[test]
  fn test_all_symbols() {
    let all_bits = Bit::all_symbols();
    let all_single_bits = MacroSymbol::<Bit, 1>::all_symbols();
    assert_eq!(
      all_single_bits
        .into_iter()
        .map(|MacroSymbol([b])| b)
        .collect_vec(),
      all_bits
    );

    let all_pair_bits = MacroSymbol::<Bit, 2>::all_symbols();
    let pair_bit_answers = vec![
      (Bit(false), Bit(false)),
      (Bit(false), Bit(true)),
      (Bit(true), Bit(false)),
      (Bit(true), Bit(true)),
    ];
    assert_eq!(
      all_pair_bits
        .into_iter()
        .map(|MacroSymbol([b, c])| (b, c))
        .collect_vec(),
      pair_bit_answers
    )
  }

  #[test]
  fn test_make_tape() {
    let sym = MacroSymbol([Bit(true), Bit(true), Bit(false), Bit(false)]);
    let mut left_ans = parse_exact(parse_tape(" |>T<| (T, 1) (F, 2)"));
    left_ans.tape_end_inf = false;
    assert_eq!(MacroMachine::make_tape(Dir::L, sym), left_ans);
    let mut right_ans = parse_exact(parse_tape("(T, 2) (F, 1) |>F<| "));
    right_ans.tape_end_inf = false;
    assert_eq!(MacroMachine::make_tape(Dir::R, sym), right_ans);
  }

  #[test]
  fn test_from_tape() {
    todo!();
  }
}
