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

use std::{collections::HashMap, fmt::Display, ops::Not};

use itertools::{repeat_n, Itertools};

use crate::{
  tape::{push_exptape, ExpTape, StepResult::*},
  turing::{
    Dir, Edge, Phase, SmallBinMachine, State, TapeSymbol,
    Trans::{self, *},
    Turing,
  },
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum MacroState<P> {
  Halted(P, usize),
  NotHalted(P, Dir),
}
use MacroState::*;

impl<P: Phase> MacroState<P> {
  fn get_state(&self) -> P {
    match self {
      &Halted(p, _) => p,
      &NotHalted(p, _) => p,
    }
  }
}

impl<P: Phase> Display for MacroState<P> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Halted(p, loc) => write!(f, "halted phase {} at loc {}", p, loc),
      NotHalted(p, dir) => write!(f, "{} at {}", p, dir),
    }
  }
}

impl<P: Phase> Phase for MacroState<P> {
  const START: Self = NotHalted(P::START, Dir::L);

  const INFINITE: Self = NotHalted(P::INFINITE, Dir::L);

  fn halted(self: Self) -> bool {
    match self {
      Halted(_, _) => true,
      NotHalted(_, _) => false,
    }
  }

  fn as_byte(self: Self) -> u8 {
    match self {
      Halted(_, _) => unreachable!("only as_byte not halting things"),
      NotHalted(phase, dir) => {
        let base_machine_byte = phase.as_byte();
        let mut out = base_machine_byte * 2;
        if dir == Dir::L {
          out -= 1;
        }
        out
      }
    }
  }
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

  fn make_tape_from_head<P>(
    state: MacroState<P>,
    MacroSymbol(arr): MacroSymbol<S, N>,
  ) -> ExpTape<S, u32> {
    let disp = match state {
      Halted(_, disp) => disp,
      NotHalted(_, Dir::L) => 0,
      NotHalted(_, Dir::R) => N - 1,
    };
    let left = ExpTape::un_splat(&mut arr[0..disp].into_iter(), false);
    let head = arr[disp];
    let right = ExpTape::un_splat(&mut arr[disp + 1..].into_iter().rev(), false);
    ExpTape { left, head, right, tape_end_inf: false }
  }

  pub fn from_fell_off_tape(
    ExpTape { left, head: _, right, tape_end_inf }: ExpTape<S, u32>,
    dir: Dir,
  ) -> Self {
    assert!(!tape_end_inf);
    //panics if the tape is the wrong size
    match dir {
      Dir::L => {
        assert_eq!(left.len(), 0);
        Self(ExpTape::splat(&mut right.iter().rev()).try_into().unwrap())
      }
      Dir::R => {
        assert_eq!(right.len(), 0);
        Self(ExpTape::splat(&mut left.iter()).try_into().unwrap())
      }
    }
  }

  fn from_tape(ExpTape { left, head, right, tape_end_inf }: ExpTape<S, u32>) -> Self {
    assert!(!tape_end_inf);
    //panics if the tape is the wrong size
    let mut out = left;
    ExpTape::push_rle(&mut out, head, false);
    for &item in right.iter().rev() {
      push_exptape(&mut out, item);
    }
    MacroSymbol(ExpTape::splat(&mut out.iter()).try_into().unwrap())
  }
}

impl<S: TapeSymbol, const N: usize> Display for MacroSymbol<S, N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for sym in self.0 {
      write!(f, "{}", sym)?;
    }
    Ok(())
  }
}

impl<S: TapeSymbol, const N: usize> TapeSymbol for MacroSymbol<S, N> {
  fn empty() -> Self {
    MacroSymbol([S::empty(); N])
  }

  fn all_symbols() -> Vec<Self> {
    Self::all_symbols()
  }
}

pub struct MacroMachine<'a, P, S, const N: usize>(
  HashMap<(MacroState<P>, MacroSymbol<S, N>), Trans<MacroState<P>, MacroSymbol<S, N>>>,
  Box<dyn Turing<P, S> + 'a>,
);

impl<'a, P: Phase, S: TapeSymbol, const N: usize> MacroMachine<'a, P, S, N> {
  // this is the eager version. it would be easy to write the lazy version as well
  pub fn new(machine: impl Turing<P, S> + 'a) -> Self {
    let mut hm = HashMap::new();
    for state in machine.all_states() {
      for dir in [Dir::L, Dir::R] {
        for macro_symbol in MacroSymbol::all_symbols() {
          let ans = Self::calculate_macro_step(&machine, state, dir, macro_symbol);
          hm.insert((NotHalted(state, dir), macro_symbol), ans);
        }
      }
    }
    Self(hm, Box::new(machine))
  }

  pub fn calculate_macro_step(
    machine: &impl Turing<P, S>,
    mut state: P,
    dir: Dir,
    sym: MacroSymbol<S, N>,
  ) -> Trans<MacroState<P>, MacroSymbol<S, N>> {
    // 1) make the tape for the machine to run on
    let mut tape = MacroSymbol::make_tape(dir, sym);
    // 2) calculate the step limit
    let step_limit: usize =
      usize::from(machine.num_states()) * S::num_symbols().pow(N.try_into().unwrap()) * N;
    let tape_len = tape.len();
    // 3) simulate up to that step limit, with 1 of 4 results:
    // a) machine loops b) machine halts c) machine falls off a side d) edge is undefined
    let mut machine_steps = 0;
    for _step in 1..=step_limit {
      state = match tape.step_extra_info(state, machine) {
        UndefinedEdge(_) => unreachable!("machine is defined"), // d
        FellOffTape(state, dir, steps) => {
          machine_steps += steps;
          if state.halted() {
            let cur_pos = match dir {
              Dir::L => N - 1,
              Dir::R => 0,
            };
            return Halt {
              state: Halted(state, cur_pos),
              symbol: MacroSymbol::from_fell_off_tape(tape, dir),
              mb_dir: Some(dir),
              steps: machine_steps,
            };
          } else {
            return Step {
              state: NotHalted(state, dir.flip()),
              symbol: MacroSymbol::from_fell_off_tape(tape, dir),
              dir,
              steps: machine_steps,
            }; // c
          }
        }
        Success(state, _, steps) => {
          machine_steps += steps;
          state
        }
        SRInfinite => return Infinite, // smaller machine infinite
      };
      assert_eq!(tape.len(), tape_len, "{}", tape);
      if state.halted() {
        return Halt {
          state: Halted(state, tape.left.len()),
          symbol: MacroSymbol::from_tape(tape),
          mb_dir: None,
          steps: machine_steps,
        }; // b
      }
    }
    return Infinite; // a
  }

  pub fn macro_step(
    &self,
    macro_state: MacroState<P>,
    sym: MacroSymbol<S, N>,
  ) -> Trans<MacroState<P>, MacroSymbol<S, N>> {
    let mb_ans = self.0.get(&(macro_state, sym));
    *mb_ans.expect(&format!("attempted to lookup {} {}", macro_state, sym))
  }

  pub fn project_down(
    macro_state: MacroState<P>,
    ExpTape { left, head, right, tape_end_inf }: ExpTape<MacroSymbol<S, N>, u32>,
  ) -> (P, ExpTape<S, u32>) {
    let mut partial_left: Vec<(S, u32)> = vec![];
    for (MacroSymbol(macro_sym), repeats) in left {
      for _ in 0..repeats {
        for sym in macro_sym {
          ExpTape::push_rle(&mut partial_left, sym, tape_end_inf);
        }
      }
    }

    let mut partial_right: Vec<(S, u32)> = vec![];
    for (MacroSymbol(macro_sym), repeats) in right {
      for _ in 0..repeats {
        for sym in macro_sym.into_iter().rev() {
          ExpTape::push_rle(&mut partial_right, sym, tape_end_inf);
        }
      }
    }

    dbg!(&partial_left, &partial_right);
    let ExpTape {
      left: sym_left,
      head,
      right: sym_right,
      tape_end_inf: _,
    } = MacroSymbol::make_tape_from_head(macro_state, head);
    dbg!(&sym_left, &sym_right);
    for (sym, repeat) in sym_left {
      for _ in 0..repeat {
        ExpTape::push_rle(&mut partial_left, sym, tape_end_inf);
      }
    }
    for (sym, repeat) in sym_right.into_iter() {
      for r in 0..repeat {
        ExpTape::push_rle(&mut partial_right, sym, tape_end_inf);
        dbg!(r, &partial_right);
      }
    }
    (
      macro_state.get_state(),
      ExpTape {
        left: partial_left,
        head,
        right: partial_right,
        tape_end_inf,
      },
    )
  }
}

impl<'a, P: Phase, S: TapeSymbol, const N: usize> Turing<MacroState<P>, MacroSymbol<S, N>>
  for MacroMachine<'a, P, S, N>
{
  fn all_states(&self) -> Vec<MacroState<P>> {
    let base_machine_states = self.1.all_states();
    let mut out = vec![];
    for base_state in base_machine_states {
      out.push(NotHalted(base_state, Dir::L));
      out.push(NotHalted(base_state, Dir::R));
    }
    out
  }

  fn step(
    &self,
    Edge(macro_state, sym): Edge<MacroState<P>, MacroSymbol<S, N>>,
  ) -> Option<Trans<MacroState<P>, MacroSymbol<S, N>>> {
    Some(self.macro_step(macro_state, sym))
  }

  fn to_compact_format(&self) -> String {
    format!("macro size {} of {}", N, self.1.to_compact_format())
  }
}

#[cfg(test)]
mod test {
  use std::num;

  use crate::{
    parse::{parse_exact, parse_tape},
    rules::Rulebook,
    turing::Bit,
    turing_examples::{all_machine_examples, get_machine},
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
    assert_eq!(MacroSymbol::make_tape(Dir::L, sym), left_ans);
    let mut right_ans = parse_exact(parse_tape("(T, 2) (F, 1) |>F<| "));
    right_ans.tape_end_inf = false;
    assert_eq!(MacroSymbol::make_tape(Dir::R, sym), right_ans);

    let sym = MacroSymbol([Bit(false), Bit(false)]);
    let mut left_ans = parse_exact(parse_tape(" |>F<| (F, 1)"));
    left_ans.tape_end_inf = false;
    assert_eq!(MacroSymbol::make_tape(Dir::L, sym), left_ans);
    let mut right_ans = parse_exact(parse_tape("(F, 1) |>F<| "));
    right_ans.tape_end_inf = false;
    assert_eq!(MacroSymbol::make_tape(Dir::R, sym), right_ans);
  }

  #[test]
  fn test_from_tape() {
    let sym = MacroSymbol([Bit(true), Bit(true), Bit(false), Bit(false)]);
    let mut tape = parse_exact(parse_tape(" |>T<| (T, 1) (F, 2)"));
    tape.tape_end_inf = false;
    assert_eq!(MacroSymbol::from_tape(tape), sym);
  }

  #[test]
  fn test_make_tape_from_head() {
    let sym = MacroSymbol([Bit(true), Bit(true), Bit(false), Bit(false)]);
    let state_l = NotHalted((), Dir::L);
    let mut ans_l = parse_exact(parse_tape(" |>T<| (T, 1) (F, 2)"));
    ans_l.tape_end_inf = false;
    assert_eq!(MacroSymbol::make_tape_from_head(state_l, sym), ans_l);

    let state_r = NotHalted((), Dir::R);
    let mut ans_r = parse_exact(parse_tape("(T, 2) (F, 1) |>F<| "));
    ans_r.tape_end_inf = false;
    assert_eq!(MacroSymbol::make_tape_from_head(state_r, sym), ans_r);

    let state_1 = Halted((), 1);
    let mut ans_1 = parse_exact(parse_tape("(T, 1) |>T<| (F, 2)"));
    ans_1.tape_end_inf = false;
    assert_eq!(MacroSymbol::make_tape_from_head(state_1, sym), ans_1);
  }

  #[test]
  fn test_project_down() {
    let ttff = MacroSymbol([Bit(true), Bit(true), Bit(false), Bit(false)]);
    let fftt = MacroSymbol([Bit(false), Bit(false), Bit(true), Bit(true)]);
    let tftf = MacroSymbol([Bit(true), Bit(false), Bit(true), Bit(false)]);

    let tape = ExpTape {
      left: vec![(ttff, 2)],
      head: tftf,
      right: vec![(ttff, 1)],
      tape_end_inf: true,
    };
    let left_ans = parse_exact(parse_tape(
      "(T, 2) (F, 2) (T, 2) (F, 2) |>T<| (F, 1) (T, 1) (F, 1) (T, 2)",
    ));
    let res = MacroMachine::project_down(NotHalted(State(1), Dir::L), tape.clone());
    println!("got res {}", res.1);
    assert_eq!(res, (State(1), left_ans));

    let right_ans = parse_exact(parse_tape(
      "(T, 2) (F, 2) (T, 2) (F, 2) (T, 1) (F, 1) (T, 1) |>F<| (T, 2)",
    ));
    let res = MacroMachine::project_down(NotHalted(State(1), Dir::R), tape.clone());
    println!("got res {}", res.1);
    assert_eq!(res, (State(1), right_ans));

    let tape = ExpTape {
      left: vec![(ttff, 2), (fftt, 1)],
      head: tftf,
      right: vec![(ttff, 1)],
      tape_end_inf: true,
    };
    let left_ans = parse_exact(parse_tape(
      "(T, 2) (F, 2) (T, 2) (F, 4) (T, 2) |>T<| (F, 1) (T, 1) (F, 1) (T, 2)",
    ));
    let res = MacroMachine::project_down(NotHalted(State(1), Dir::L), tape.clone());
    println!("got res {}", res.1);
    assert_eq!(res, (State(1), left_ans));

    let right_ans = parse_exact(parse_tape(
      "(T, 2) (F, 2) (T, 2) (F, 4) (T, 3) (F, 1) (T, 1) |>F<| (T, 2)",
    ));
    let res = MacroMachine::project_down(NotHalted(State(1), Dir::R), tape.clone());
    println!("got res {}", res.1);
    assert_eq!(res, (State(1), right_ans));

    let ffft = MacroSymbol([Bit(false), Bit(false), Bit(false), Bit(true)]);
    let tttf = MacroSymbol([Bit(true), Bit(true), Bit(true), Bit(false)]);
    let tape = ExpTape {
      left: vec![(ffft, 1)],
      head: tttf,
      right: vec![],
      tape_end_inf: true,
    };
    let ans = parse_exact(parse_tape("(T, 1) |>T<| (T, 2)"));
    let res = MacroMachine::project_down(NotHalted(State(1), Dir::L), tape);
    println!("got res {}", res.1);
    assert_eq!(res, (State(1), ans));
  }

  fn simultaneous_step_macro_step<P: Phase, S: TapeSymbol, const N: usize>(
    machine: &impl Turing<P, S>,
    macro_machine: &impl Turing<MacroState<P>, MacroSymbol<S, N>>,
    normal_tape: &mut ExpTape<S, u32>,
    mut normal_state: P,
    macro_tape: &mut ExpTape<MacroSymbol<S, N>, u32>,
    macro_state: MacroState<P>,
    step: u32,
  ) -> Option<(P, MacroState<P>)> {
    let (proj_macro_state, proj_macro_tape) =
      MacroMachine::project_down(macro_state, macro_tape.clone());
    assert_eq!(normal_state, proj_macro_state, "step: {}", step);
    assert_eq!(
      normal_tape, &proj_macro_tape,
      "step: {}\nmacro_tape: {}",
      step, macro_tape
    );

    let (new_macro_state, steps) = match macro_tape.step_extra_info(macro_state, macro_machine) {
      UndefinedEdge(_) => panic!("machine is defined"),
      FellOffTape(_, _, _) => panic!("fell off tape unexpectedly"),
      SRInfinite => return None,
      Success(new_macro_state, _rs, steps) => (new_macro_state, steps),
    };

    for _ in 0..steps {
      if normal_state.halted() {
        panic!(
          "machine diverged: {} {}\nvs\n{} {}",
          new_macro_state, macro_tape, normal_state, normal_tape
        )
      }
      normal_state = normal_tape
        .step_extra_info(normal_state, machine)
        .expect_success()
        .0;
    }
    return Some((normal_state, new_macro_state));
  }

  fn macro_is_same_as_base<P: Phase, S: TapeSymbol, const N: usize>(
    machine: &(impl Turing<P, S> + Clone),
    num_steps: u32,
  ) {
    let macro_machine: MacroMachine<P, S, N> = MacroMachine::new(machine.clone());

    let mut normal_tape = ExpTape::new(true);
    let mut normal_state = P::START;
    let mut macro_tape = ExpTape::new(true);
    let mut macro_state = MacroState::START;
    for step in 1..num_steps + 1 {
      (normal_state, macro_state) = match simultaneous_step_macro_step(
        machine,
        &macro_machine,
        &mut normal_tape,
        normal_state,
        &mut macro_tape,
        macro_state,
        step,
      ) {
        Some(ans) => ans,
        None => return,
      };
      if normal_state.halted() || macro_state.halted() {
        assert!(normal_state.halted() && macro_state.halted());
        return;
      }
    }
    println!("final tape: {}\nand\n{}", normal_tape, macro_tape);
  }

  #[test]
  fn test_macro_is_same_as_base() {
    for (name, machine) in all_machine_examples() {
      dbg!(name);
      macro_is_same_as_base::<_, _, 2>(&machine, 100);
      macro_is_same_as_base::<_, _, 3>(&machine, 100);
      macro_is_same_as_base::<_, _, 4>(&machine, 100);
      macro_is_same_as_base::<_, _, 5>(&machine, 100);
      macro_is_same_as_base::<_, _, 6>(&machine, 100);
      macro_is_same_as_base::<_, _, 10>(&machine, 100);
    }
  }
}
