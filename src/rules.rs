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

use proptest::{prelude::*, sample::select};
use smallvec::{smallvec, SmallVec};
use std::{collections::HashMap, fmt::Display};

use crate::turing::{
  Dir::{L, R},
  Edge, State, TapeSymbol, Trans, Turing, Bit,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Var(pub u8);

impl Display for Var {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      write!(f, "x_{}", self.0)
  }
}

//ax + n
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct AffineVar {
  pub n: u32,
  pub a: u32,
  pub var: Var,
}

impl AffineVar {
  pub fn constant(n: u32) -> Self {
    Self {n, a: 0, var: Var(0)}
  }

  pub fn sub(&self, x: u32) -> u32 {
    let AffineVar { n, a, var: _var } = self;
    return n + a * x;
  }

  pub fn sub_map(&self, hm: &HashMap<Var, u32>) -> u32 {
    let &x = hm.get(&self.var).unwrap();
    self.sub(x)
  }
}

impl Display for AffineVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} + {}*{}", self.n, self.a, self.var)
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

//todo: figure out like modules or something
// impl Config<S> {
//   fn from_tape_state(state: State, exptape : ExpTape)
// }

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

pub mod parse {
  
  use nom::{
    bytes::complete::{tag, is_a},
    character::complete::{char, one_of},
    combinator::{map_res, recognize, map},
    multi::{many0, many1, separated_list0},
    sequence::{terminated, Tuple, delimited, separated_pair},
    IResult, branch::alt, error::{ParseError, FromExternalError},
  };
  use std::num::ParseIntError;

use crate::turing::{Bit, State};

use super::{Var, AffineVar, Config, Rule};
  
  fn parse_int<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)
  }

  fn parse_u32<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, u32, E> {
    map_res(parse_int,
      |out: &str| u32::from_str_radix(out, 10),
    )(input)
  }

  fn parse_u8<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, u8, E> {
    map_res(parse_int, |out: &str| u8::from_str_radix(out, 10))(input)
  }

  fn parse_var<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, Var, E> {
    map(parse_u8, |out: u8| Var(out))(input)
  }

  /*
  in 100 steps we turn
  phase: 3  (F, 1) (T, 1 + 1*x_0 ) |>T<|
  into:
  phase: 1  (T, 1) |>F<|(F, 0 + 1*x_0 ) (T, 1)
  */

  pub fn parse_avar<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, AffineVar, E> {
    // 3 + 2*x_0
    let (input, (n, _, a, _, var)) =
      (parse_u32, tag(" + "), parse_u32, tag("*x_"), parse_var).parse(input)?;
    let avar = AffineVar { n, a, var };
    Ok((input, avar))
  }

  pub fn parse_count<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, AffineVar, E> {
    let parse_u32_to_avar = map(parse_u32, |out: u32| AffineVar{n: out, a:0, var: Var(0)});
    alt((parse_avar, parse_u32_to_avar))(input)
  }

  pub fn parse_bit<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Bit, E> {
    map(alt((char('T'), char('F'))), |c| match c {
      'T' => Bit(true), 
      'F' => Bit(false), 
      _ => unreachable!("only parsed the two chars")
    })(input)
  }

  pub fn parse_count_tuple<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, (Bit, AffineVar), E> {
    delimited(tag("("), separated_pair(parse_bit, tag(", "), parse_count), tag(")"))(input)
  }

  pub fn parse_config_tape_side<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, Vec<(Bit, AffineVar)>, E> {
    separated_list0(char(' '), parse_count_tuple)(input)
  }

  pub fn parse_u32_tuple<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, (Bit, u32), E> {
    delimited(tag("("), separated_pair(parse_bit, tag(", "), parse_u32), tag(")"))(input)
  }

  pub fn parse_tape_side<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, Vec<(Bit, u32)>, E> {
    separated_list0(char(' '), parse_u32_tuple)(input)
  }

  pub fn parse_config<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(input: &'a str) -> IResult<&str, Config<Bit>, E> {
    let (input, (_, state_digit, _, left, _, head, _, mut right)) = 
      (tag("phase: "), parse_u8, tag("  "), parse_config_tape_side, 
        tag(" |>"), parse_bit, tag("<| "), parse_config_tape_side).parse(input)?;
    right.reverse();
    Ok((input, Config{state: State(state_digit), left, head, right}))
  }

  pub fn parse_rule(input: &str) -> IResult<&str, Rule<Bit>> {
    let (input, (start, _, end)) = (parse_config, tag("\ninto:\n"), parse_config).parse(input)?;
    Ok((input, Rule{start, end}))
  }

  mod test {
    use nom::Finish;
    use proptest::{strategy::Strategy, prelude::*};

    use super::*;

    #[test]
    fn test_parse_avar() {
      let ans = parse_avar::<nom::error::Error<&str>>("3 + 5*x_0");
      assert_eq!(ans, Ok(("", AffineVar{n: 3, a: 5, var: Var(0)})));
      assert_eq!(parse_avar::<nom::error::Error<&str>>("7 + 234*x_11"), Ok(("", AffineVar{n: 7, a: 234, var: Var(11)})));
      assert_eq!(parse_avar::<nom::error::Error<&str>>("118 + 5*x_0"), Ok(("", AffineVar{n: 118, a: 5, var: Var(0)})));

      assert!(parse_avar::<nom::error::Error<&str>>("3 + 5* x_0").is_err());
    }

    #[test]
    fn avar_disp() {
      assert_eq!(format!("{}", AffineVar{n: 3, a: 5, var: Var(0)}), "3 + 5*x_0");
    }

    #[test]
    fn test_parse_count() {
      assert_eq!(parse_count::<nom::error::Error<&str>>("3 + 5*x_0"), Ok(("", AffineVar{n: 3, a: 5, var: Var(0)})));
      assert_eq!(parse_count::<nom::error::Error<&str>>("7 + 234*x_11"), Ok(("", AffineVar{n: 7, a: 234, var: Var(11)})));
      assert_eq!(parse_count::<nom::error::Error<&str>>("7"), Ok(("", AffineVar{n: 7, a: 0, var: Var(0)})));
    }

    #[test]
    fn test_parse_tuple() {
      assert_eq!(parse_count_tuple::<nom::error::Error<&str>>("(F, 1)"), Ok(("", (Bit(false), AffineVar::constant(1)))));
      assert_eq!(parse_count_tuple::<nom::error::Error<&str>>("(F, 0 + 1*x_0)"), Ok(("", (Bit(false), AffineVar{n: 0, a: 1, var: Var(0)}))));
      assert_eq!(parse_count_tuple::<nom::error::Error<&str>>("(T, 1 + 3*x_2)"), Ok(("", (Bit(true), AffineVar{n: 1, a: 3, var: Var(2)}))));
      assert!(parse_count_tuple::<nom::error::Error<&str>>("(T, 1 + 3*x_2").is_err())
    }

    #[test]
    fn test_parse_tape_side() {
      assert_eq!(parse_config_tape_side::<nom::error::Error<&str>>("(F, 1) (T, 1 + 1*x_0)"), 
        Ok(("", vec![(Bit(false), AffineVar::constant(1)), 
            (Bit(true), AffineVar{n: 1, a: 1, var:Var(0)})])));
      assert_eq!(parse_config_tape_side::<nom::error::Error<&str>>("(F, 0 + 1*x_0) (T, 1)"),
        Ok(("", vec![(Bit(false), AffineVar{n: 0, a:1, var:Var(0)}),
              (Bit(true), AffineVar::constant(1))])));
    }

    #[test]
    fn test_parse_config() {
      let start = Config{state: State(3), left: vec![(Bit(false), AffineVar::constant(1)), 
        (Bit(true), AffineVar{n: 1, a: 1, var:Var(0)})], head: Bit(true), 
      right: vec![]};
      let inp = "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| ";
      let ans: Result<(&str, Config<Bit>), nom::error::VerboseError<&str>> = parse_config(inp).finish();
      assert_eq!(ans, Ok(("", start)));

    }

    #[test]
    fn test_parse_rule() {
      let start = Config{state: State(3), left: vec![(Bit(false), AffineVar::constant(1)), 
        (Bit(true), AffineVar{n: 1, a: 1, var:Var(0)})], head: Bit(true), 
      right: vec![]};
      let end = Config{state: State(1), left: vec![(Bit(true), AffineVar::constant(1))], head: Bit(false), 
      right: vec![(Bit(true), AffineVar::constant(1)), (Bit(false), AffineVar{n: 0, a:1, var:Var(0)})]};
      let rule_str = "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| \ninto:\nphase: 1  (T, 1) |>F<| (F, 0 + 1*x_0) (T, 1)";
      assert_eq!(parse_rule(rule_str), Ok(("", Rule{start, end})));
    }
    fn avar_strategy() -> impl Strategy<Value = AffineVar> {
      (any::<u32>(), any::<u32>(), any::<u8>())
      .prop_map(|(n, a, v_num)| AffineVar{n, a, var: Var(v_num)})
    }
    
    proptest! {
      #[test]
      fn avar_roundtrip(avar in avar_strategy()) {
        assert_eq!(parse_avar::<nom::error::Error<&str>>(&format!("{}", avar)), Ok(("", avar)));
      }
    }
  
  }
}

mod test {
  use nom::Finish;

use crate::turing::{get_machine, Bit};

  use super::*;

  #[test]
  fn affinevar_sub() {
    let three_fifty = AffineVar {
      n: 50,
      a: 3,
      var: Var(0),
    };
    assert_eq!(three_fifty.sub(6), 68);
    assert_eq!(three_fifty.sub(0), 50);
    let two_x_plus_seven = AffineVar {
      n: 7,
      a: 2,
      var: Var(1),
    };
    assert_eq!(two_x_plus_seven.sub(19), 45);
    assert_eq!(two_x_plus_seven.sub(3), 13);
  }

  #[test]
  fn affinevar_sub_map() {
    let mut hm = HashMap::new();
    hm.insert(Var(0), 6);
    hm.insert(Var(1), 19);

    let three_fifty = AffineVar {
      n: 50,
      a: 3,
      var: Var(0),
    };
    let two_x_plus_seven = AffineVar {
      n: 7,
      a: 2,
      var: Var(1),
    };

    assert_eq!(three_fifty.sub_map(&hm), 68);
    assert_eq!(two_x_plus_seven.sub_map(&hm), 45);
  }

  #[test]
  fn chain_rules_detected() {
    let bb2 = get_machine("bb2");
    assert_eq!(detect_chain_rules(&bb2), vec![]);
    let binary_counter = get_machine("binary_counter");
    let detected_rules = detect_chain_rules(&binary_counter);
    // todo this is absolutely gross
    let rule1 = Rule {
      start: Config {
        state: State(1),
        left: vec![],
        head: Bit(true),
        right: vec![(
          Bit(true),
          AffineVar {
            n: 0,
            a: 1,
            var: Var(0),
          },
        )],
      },
      end: Config {
        state: State(1),
        left: vec![(
          Bit(false),
          AffineVar {
            n: 0,
            a: 1,
            var: Var(0),
          },
        )],
        head: Bit(false),
        right: vec![],
      },
    };
    let rule2 = Rule {
      start: Config {
        state: State(3),
        left: vec![(
          Bit(true),
          AffineVar {
            n: 0,
            a: 1,
            var: Var(0),
          },
        )],
        head: Bit(true),
        right: vec![],
      },
      end: Config {
        state: State(3),
        left: vec![],
        head: Bit(true),
        right: vec![(
          Bit(true),
          AffineVar {
            n: 0,
            a: 1,
            var: Var(0),
          },
        )],
      },
    };
    assert_eq!(detected_rules, vec![rule1, rule2]);
  }
}

