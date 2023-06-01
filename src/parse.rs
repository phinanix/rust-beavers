use defaultmap::defaulthashmap;
use nom::{
  branch::alt,
  bytes::complete::{is_a, tag},
  character::complete::{char, one_of},
  combinator::{map, map_res, recognize},
  error::{FromExternalError, ParseError},
  multi::{many0, many1, separated_list0},
  sequence::{delimited, separated_pair, terminated, Tuple},
  IResult, InputIter,
};
use std::num::ParseIntError;

use crate::{
  rules::{AVarSum, AffineVar, Config, Rule, Var},
  tape::ExpTape,
  turing::{Bit, State, AB, HALT},
};

pub fn parse_exact<X>(res: IResult<&str, X>) -> X {
  let (leftover, x) = res.unwrap();
  assert_eq!(leftover, "");
  x
}

fn parse_int<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
  recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)
}

fn parse_u32<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, u32, E> {
  map_res(parse_int, |out: &str| u32::from_str_radix(out, 10))(input)
}

fn parse_u8<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, u8, E> {
  map_res(parse_int, |out: &str| u8::from_str_radix(out, 10))(input)
}

fn parse_state_number<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, State, E> {
  map(parse_u8, |out| State(out))(input)
}

fn parse_state_letter<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, State, E> {
  let (input, letter) = one_of(AB)(input)?;
  let state = State(AB.find(letter).unwrap().try_into().unwrap());
  Ok((input, state))
}

fn parse_var<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, Var, E> {
  map(parse_u8, |out: u8| Var(out))(input)
}

/*
in 100 steps we turn
phase: 3  (F, 1) (T, 1 + 1*x_0 ) |>T<|
into:
phase: 1  (T, 1) |>F<|(F, 0 + 1*x_0 ) (T, 1)
*/

pub fn parse_avar_gen<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, AffineVar, E> {
  // 3 + 2*x_0
  let (input, (n, _, a, _, var)) =
    (parse_u32, tag(" + "), parse_u32, tag("*x_"), parse_var).parse(input)?;
  let avar = AffineVar { n, a, var };
  Ok((input, avar))
}

pub fn parse_avar(input: &str) -> IResult<&str, AffineVar> {
  parse_avar_gen(input)
}

fn parse_var_times<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, (u32, Var), E> {
  // " + 1*x_1"
  let (input, (_, a, _, var)) = (tag(" + "), parse_u32, tag("*x_"), parse_var).parse(input)?;
  Ok((input, (a, var)))
}

pub fn parse_avar_sum_gen<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
>(
  input: &'a str,
) -> IResult<&str, AVarSum, E> {
  // 1 + 1*x_0 + 1*x_1
  let (input, n) = parse_u32(input)?;
  let (input, vars) = many0(parse_var_times)(input)?;
  let mut var_map = defaulthashmap! {};
  for (a, v) in vars {
    var_map[v] = a;
  }
  Ok((input, AVarSum { n, var_map }))
}

pub fn parse_avar_sum(input: &str) -> IResult<&str, AVarSum> {
  parse_avar_sum_gen(input)
}

pub fn parse_num_or_avar<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, AffineVar, E> {
  let parse_u32_to_avar = map(parse_u32, |out: u32| AffineVar {
    n: out,
    a: 0,
    var: Var(0),
  });
  alt((parse_avar_gen, parse_u32_to_avar))(input)
}

pub fn parse_bit<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Bit, E> {
  map(alt((char('T'), char('F'))), |c| match c {
    'T' => Bit(true),
    'F' => Bit(false),
    _ => unreachable!("only parsed the two chars"),
  })(input)
}

pub fn parse_num_avar_tuple<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
>(
  input: &'a str,
) -> IResult<&str, (Bit, AffineVar), E> {
  delimited(
    tag("("),
    separated_pair(parse_bit, tag(", "), parse_num_or_avar),
    tag(")"),
  )(input)
}

pub fn parse_avarsum_tuple<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
>(
  input: &'a str,
) -> IResult<&str, (Bit, AVarSum), E> {
  delimited(
    tag("("),
    separated_pair(parse_bit, tag(", "), parse_avar_sum_gen),
    tag(")"),
  )(input)
}

pub fn parse_config_tape_side_gen<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
>(
  input: &'a str,
) -> IResult<&str, Vec<(Bit, AffineVar)>, E> {
  separated_list0(char(' '), parse_num_avar_tuple)(input)
}

pub fn parse_config_tape_side(input: &str) -> IResult<&str, Vec<(Bit, AffineVar)>> {
  parse_config_tape_side_gen(input)
}

pub fn parse_end_config_tape_side_gen<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
>(
  input: &'a str,
) -> IResult<&str, Vec<(Bit, AVarSum)>, E> {
  separated_list0(char(' '), parse_avarsum_tuple)(input)
}

pub fn parse_end_config_tape_side(input: &str) -> IResult<&str, Vec<(Bit, AVarSum)>> {
  parse_end_config_tape_side_gen(input)
}

pub fn parse_u32_tuple<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, (Bit, u32), E> {
  delimited(
    tag("("),
    separated_pair(parse_bit, tag(", "), parse_u32),
    tag(")"),
  )(input)
}

pub fn parse_tape_side<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, Vec<(Bit, u32)>, E> {
  separated_list0(char(' '), parse_u32_tuple)(input)
}

pub fn parse_tape(input: &str) -> IResult<&str, ExpTape<Bit, u32>> {
  let (input, (left, _, head, _, mut right)) = (
    parse_tape_side,
    tag(" |>"),
    parse_bit,
    tag("<| "),
    parse_tape_side,
  )
    .parse(input)?;
  right.reverse();
  Ok((input, ExpTape { left, head, right, tape_end_inf: true }))
}

pub fn parse_config<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, Config<Bit, AffineVar>, E> {
  let (input, (_, state, _, left, _, head, _, mut right)) = (
    tag("phase: "),
    alt((parse_state_number, parse_state_letter)),
    tag("  "),
    parse_config_tape_side_gen,
    tag(" |>"),
    parse_bit,
    tag("<| "),
    parse_config_tape_side_gen,
  )
    .parse(input)?;
  right.reverse();
  Ok((input, Config { state, left, head, right }))
}

pub fn parse_end_config<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, Config<Bit, AVarSum>, E> {
  let (input, (_, state, _, left, _, head, _, mut right)) = (
    tag("phase: "),
    alt((parse_state_number, parse_state_letter)),
    tag("  "),
    parse_end_config_tape_side_gen,
    tag(" |>"),
    parse_bit,
    tag("<| "),
    parse_end_config_tape_side_gen,
  )
    .parse(input)?;
  right.reverse();
  Ok((input, Config { state, left, head, right }))
}

pub fn parse_rule(input: &str) -> IResult<&str, Rule<Bit>> {
  let (input, (start, _, end)) = (parse_config, tag("\ninto:\n"), parse_end_config).parse(input)?;
  Ok((input, Rule { start, end }))
}

pub fn parse_half_tape(input: &str) -> Vec<(Bit, AffineVar)> {
  let mut out = parse_exact(parse_config_tape_side(input));
  out.reverse();
  out
}

pub fn parse_end_half_tape(input: &str) -> Vec<(Bit, AVarSum)> {
  let mut out = parse_exact(parse_end_config_tape_side(input));
  out.reverse();
  out
}

mod test {
  use nom::Finish;
  use proptest::{prelude::*, strategy::Strategy};

  use super::*;

  #[test]
  fn test_parse_avar() {
    let ans = parse_avar_gen::<nom::error::Error<&str>>("3 + 5*x_0");
    assert_eq!(ans, Ok(("", AffineVar { n: 3, a: 5, var: Var(0) })));
    assert_eq!(
      parse_avar_gen::<nom::error::Error<&str>>("7 + 234*x_11"),
      Ok(("", AffineVar { n: 7, a: 234, var: Var(11) }))
    );
    assert_eq!(
      parse_avar_gen::<nom::error::Error<&str>>("118 + 5*x_0"),
      Ok(("", AffineVar { n: 118, a: 5, var: Var(0) }))
    );

    assert!(parse_avar_gen::<nom::error::Error<&str>>("3 + 5* x_0").is_err());
  }

  #[test]
  fn test_parse_avar_sum() {
    let parser_ans = parse_avar_sum("7");
    let ans = AVarSum::from(AffineVar { n: 7, a: 0, var: Var(0) });
    assert_eq!(parser_ans, Ok(("", ans)));

    let parser_ans = parse_avar_sum("1 + 1*x_0");
    let ans = AVarSum::from(AffineVar { n: 1, a: 1, var: Var(0) });
    assert_eq!(parser_ans, Ok(("", ans)));

    let parser_ans = parse_avar_sum("1 + 1*x_0 + 1*x_1");
    let mut ans = AVarSum::from(AffineVar { n: 1, a: 1, var: Var(0) });
    ans.add_avar(AffineVar { n: 0, a: 1, var: Var(1) });
    assert_eq!(parser_ans, Ok(("", ans)));
  }

  #[test]
  fn avar_disp() {
    assert_eq!(
      format!("{}", AffineVar { n: 3, a: 5, var: Var(0) }),
      "3 + 5*x_0"
    );
  }

  #[test]
  fn test_parse_count() {
    assert_eq!(
      parse_num_or_avar::<nom::error::Error<&str>>("3 + 5*x_0"),
      Ok(("", AffineVar { n: 3, a: 5, var: Var(0) }))
    );
    assert_eq!(
      parse_num_or_avar::<nom::error::Error<&str>>("7 + 234*x_11"),
      Ok(("", AffineVar { n: 7, a: 234, var: Var(11) }))
    );
    assert_eq!(
      parse_num_or_avar::<nom::error::Error<&str>>("7"),
      Ok(("", AffineVar { n: 7, a: 0, var: Var(0) }))
    );
  }

  #[test]
  fn test_parse_tuple() {
    assert_eq!(
      parse_num_avar_tuple::<nom::error::Error<&str>>("(F, 1)"),
      Ok(("", (Bit(false), AffineVar::constant(1))))
    );
    assert_eq!(
      parse_num_avar_tuple::<nom::error::Error<&str>>("(F, 0 + 1*x_0)"),
      Ok(("", (Bit(false), AffineVar { n: 0, a: 1, var: Var(0) })))
    );
    assert_eq!(
      parse_num_avar_tuple::<nom::error::Error<&str>>("(T, 1 + 3*x_2)"),
      Ok(("", (Bit(true), AffineVar { n: 1, a: 3, var: Var(2) })))
    );
    assert!(parse_num_avar_tuple::<nom::error::Error<&str>>("(T, 1 + 3*x_2").is_err())
  }

  #[test]
  fn test_parse_tape_side() {
    assert_eq!(
      parse_config_tape_side_gen::<nom::error::Error<&str>>("(F, 1) (T, 1 + 1*x_0)"),
      Ok((
        "",
        vec![
          (Bit(false), AffineVar::constant(1)),
          (Bit(true), AffineVar { n: 1, a: 1, var: Var(0) })
        ]
      ))
    );
    assert_eq!(
      parse_config_tape_side_gen::<nom::error::Error<&str>>("(F, 0 + 1*x_0) (T, 1)"),
      Ok((
        "",
        vec![
          (Bit(false), AffineVar { n: 0, a: 1, var: Var(0) }),
          (Bit(true), AffineVar::constant(1))
        ]
      ))
    );
  }

  #[test]
  fn test_parse_config() {
    let start = Config {
      state: State(3),
      left: vec![
        (Bit(false), AffineVar::constant(1)),
        (Bit(true), AffineVar { n: 1, a: 1, var: Var(0) }),
      ],
      head: Bit(true),
      right: vec![],
    };
    let inp = "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| ";
    let ans: Result<(&str, Config<Bit, AffineVar>), nom::error::VerboseError<&str>> =
      parse_config(inp).finish();
    assert_eq!(ans, Ok(("", start)));
  }

  #[test]
  fn test_parse_rule() {
    let start = Config {
      state: State(3),
      left: vec![
        (Bit(false), AffineVar::constant(1)),
        (Bit(true), AffineVar { n: 1, a: 1, var: Var(0) }),
      ],
      head: Bit(true),
      right: vec![],
    };
    let end = Config {
      state: State(1),
      left: vec![(Bit(true), AffineVar::constant(1))],
      head: Bit(false),
      right: vec![
        (Bit(true), AffineVar::constant(1)),
        (Bit(false), AffineVar { n: 0, a: 1, var: Var(0) }),
      ],
    };
    let rule_str =
      "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| \ninto:\nphase: 1  (T, 1) |>F<| (F, 0 + 1*x_0) (T, 1)";
    assert_eq!(
      parse_rule(rule_str),
      Ok(("", Rule { start, end: Config::from_avars(end) }))
    );
  }
  fn avar_strategy() -> impl Strategy<Value = AffineVar> {
    (any::<u32>(), any::<u32>(), any::<u8>()).prop_map(|(n, a, v_num)| AffineVar {
      n,
      a,
      var: Var(v_num),
    })
  }

  proptest! {
    #[test]
    fn avar_roundtrip(avar in avar_strategy()) {
      assert_eq!(parse_avar_gen::<nom::error::Error<&str>>(&format!("{}", avar)), Ok(("", avar)));
    }
  }
}
