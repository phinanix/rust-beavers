use itertools::{zip_eq, Itertools};
use std::cmp::Ordering::*;
use std::collections::HashMap;

use crate::{
  rules::{get_newest_var, AVarSum, AffineVar, Config, Rule, SymbolVar, Var},
  turing::{Phase, TapeSymbol},
};

/* the rules:
a thing can be internal or external
external takes precedence
if a thing happens multiple times, then it must agree
the only thing that can disagree is it can be first internal and then external as long as they
are equal (though this should never happen with current code I think?)
internal -> changing
external -> static
 */
#[derive(Debug)]
pub struct VarChainMap {
  pub changing_hm: HashMap<Var, SymbolVar>,
  pub static_hm: HashMap<Var, AffineVar>,
  pub lower_bound_hm: HashMap<Var, u32>,
}

impl VarChainMap {
  pub fn new() -> VarChainMap {
    VarChainMap {
      changing_hm: HashMap::new(),
      static_hm: HashMap::new(),
      lower_bound_hm: HashMap::new(),
    }
  }

  pub fn add_changing(&mut self, var: Var, svar: SymbolVar) -> Option<()> {
    if let Some(&prev_svar) = self.changing_hm.get(&var) {
      if prev_svar != svar {
        return None;
      }
    } else {
      self.changing_hm.insert(var, svar);
    };
    // if let Some(&avar) = self.static_hm.get(&var) {
    //   if avar != svar.into() {
    //     return None;
    //   }
    // };
    Some(())
  }

  pub fn add_static(&mut self, var: Var, avar: AffineVar) -> Option<()> {
    assert_ne!(avar, 0.into());
    if let Some(&prev_avar) = self.static_hm.get(&var) {
      if prev_avar != avar {
        return None;
      }
    } else {
      self.static_hm.insert(var, avar);
    };
    // if let Some(&prev_svar) = self.changing_hm.get(&var) {
    //   if prev_svar != avar.into() {
    //     return None;
    //   }
    // };
    Some(())
  }

  pub fn lower_bound(&mut self, var: Var, lb: u32) -> Option<()> {
    let cur_lb = if let Some(&prev_lb) = self.lower_bound_hm.get(&var) {
      prev_lb.max(lb)
    } else {
      lb
    };
    self.lower_bound_hm.insert(var, cur_lb);
    if let Some(&AffineVar { n, a: _, var: _ }) = self.static_hm.get(&var) {
      if n < cur_lb {
        return None;
      }
    }
    Some(())
  }
}

pub fn chain_var(
  var_chain_map: &mut VarChainMap,
  start: AffineVar,
  end: &AVarSum,
  chaining_var: Var,
) -> Option<(AffineVar, AVarSum)> {
  /*
  internal hm is like, when you chain (F, x) to (F, x+1), you have set x = x+1
  so you couldn't somewhere else set x = x+2
  external hm is like, when you chain (F, x) to (F, 3), you have set x = 3
  so not only can x not be anything except 3 anywhere else, you sub 3 for x everywhere else
  internal / external => changing / static
   */
  match start {
    AffineVar { n, a: 0, var: _var } => {
      if end.var_map.is_empty() {
        // this case is like 5 -> 8
        if n == end.n {
          Some((start, end.clone()))
        } else {
          None
        }
      } else {
        // this case is like 5 -> x+3
        match end.var_map.iter().exactly_one() {
          Ok((&end_var, &end_a)) => {
            let int_match = n.checked_sub(end.n)?;
            if int_match % end_a == 0 {
              var_chain_map.add_static(end_var, (int_match / end_a).into())?;
              Some((start, AVarSum::constant(n))) // these are equal
            } else {
              None
            }
          }
          Err(_) => {
            println!("tried to chain {} into {} and couldn't #1", start, end);
            return None;
          }
        }
      }
    }
    AffineVar { n, a, var } => {
      if end.var_map.is_empty() {
        // this case is like x+3 -> 5
        let int_match = end.n.checked_sub(n)?;
        if int_match % a == 0 {
          var_chain_map.add_static(var, (int_match / a).into())?;
          Some((AffineVar::constant(end.n), end.clone())) // these are equal
        } else {
          None
        }
      } else {
        // this case is like x+3 -> y+2
        match end.var_map.iter().exactly_one() {
          Ok((&end_var, &end_a)) => {
            if var != end_var || a != end_a {
              println!("tried to chain {} into {} and couldn't #2", start, end);
              return None;
            }
            // when we match ax + n to ay + m we learn the internal fact
            // x -> y + (m-n)/a
            let diff: i32 = i32::try_from(end.n).unwrap() - i32::try_from(n).unwrap();
            let a_i32 = i32::try_from(a).unwrap();
            if diff % a_i32 != 0 {
              return None;
            }
            var_chain_map.add_changing(var, SymbolVar { n: (diff / a_i32), a: 1, var })?;
            if n <= end.n {
              let diff = end.n - n;
              // (ax + n, ax + m) -> (ax + n, ax + n + k*(m - n))
              let mut end_out: AVarSum = start.into();
              if diff > 0 {
                end_out.add_avar(AffineVar { n: 0, a: diff, var: chaining_var });
              }
              Some((start, end_out))
            } else {
              // None
              if a > 1 {
                println!("chain {} into {}!", start, end);
              }
              let decrease_amt = n - end.n;
              if a == decrease_amt {
                /* (ax + n, ax + m), a = n - m,
                   (ax + m + a, ax + m) chains to
                   (ax + n, n) & k = x
                */
                let end_out = AVarSum::constant(n);
                // add k = x to map
                var_chain_map.add_static(chaining_var, AffineVar { n: 0, a: 1, var: start.var })?;
                Some((start, end_out))
              } else if a == 1 {
                // return None;
                //(x + d + c, x + c) -> (x + d + c, d + c) + x = dk
                let end_out = AVarSum::constant(n);
                // add x = dk to map
                var_chain_map
                  .add_static(var, AffineVar { n: 0, a: decrease_amt, var: chaining_var })?;
                Some((start, end_out))
              } else {
                println!("tried to chain {} into {} and couldn't #5", start, end);
                None
              }
            }
          }
          Err(_) => {
            println!("tried to chain {} into {} and couldn't #3", start, end);
            None
          }
        }
      }
    }
  }
}

pub fn chain_var_end(
  var_chain_map: &mut VarChainMap,
  start: AffineVar,
  end: &AVarSum,
  chaining_var: Var,
) -> Option<(AffineVar, AVarSum)> {
  /*
  (x, 3) -> lower bound x to 3 (or x -> y+3) then (3+y, 3) -> (3+yk, 3)
  (x, y) -> lower bound x to y and y to x ??

   */
  match start {
    AffineVar { n, a: 0, var: _var } => {
      if end.var_map.is_empty() {
        match n.cmp(&end.n) {
          Equal => Some((start, end.clone())),
          Less => {
            //(3, 4) -> (3, 3+k)
            let diff = end.n.checked_sub(n).unwrap();
            let end_out = AffineVar { n, a: diff, var: chaining_var };
            Some((start, end_out.into()))
          }
          Greater => {
            // (5, 3) -> (3 + 2k, 3)
            let diff = n.checked_sub(end.n).unwrap();
            let start_out = AffineVar { n: end.n, a: diff, var: chaining_var };
            Some((start_out, end.clone()))
          }
        }
      } else {
        match end.var_map.iter().exactly_one() {
          Ok((&_end_var, &_end_a)) => {
            println!("tried to endchain {} into {} and couldn't #1", start, end);
            None
          }
          Err(_) => {
            println!("tried to endchain {} into {} and couldn't #2", start, end);
            None
          }
        }
      }
    }
    AffineVar { n, a, var } => {
      if end.var_map.is_empty() {
        println!("tried to endchain {} into {} and couldn't #3", start, end);
        None
      } else {
        match end.var_map.iter().exactly_one() {
          Ok((&end_var, &end_a)) => {
            if var != end_var || a != end_a {
              println!("tried to endchain {} into {} and couldn't #4", start, end);
              return None;
            }
            // when we match ax + n to ay + m we learn the internal fact
            // x -> y + (m-n)/a
            let diff: i32 = i32::try_from(end.n).unwrap() - i32::try_from(n).unwrap();
            let a_i32 = i32::try_from(a).unwrap();
            if diff % a_i32 != 0 {
              return None;
            }
            var_chain_map.add_changing(var, SymbolVar { n: (diff / a_i32), a: 1, var })?;
            if n <= end.n {
              let diff = end.n - n;
              // (ax + n, ax + m) -> (ax + n, ax + n + k*(m - n))
              let mut end_out: AVarSum = start.into();
              if diff > 0 {
                end_out.add_avar(AffineVar { n: 0, a: diff, var: chaining_var });
              }
              Some((start, end_out))
            } else {
              // None
              if a > 1 {
                println!("chain {} into {}!", start, end);
              }
              let decrease_amt = n - end.n;
              if a % decrease_amt == 0 {
                /* (ax + n, ax + m), d = n - m, a = dr
                   (drx + n, drx + m) chains to
                   (drx + n, n) & k = rx
                */
                let rem = a / decrease_amt;
                let end_out = AVarSum::constant(n);
                // add k = rx to map
                var_chain_map
                  .add_static(chaining_var, AffineVar { n: 0, a: rem, var: start.var })?;
                Some((start, end_out))
              } else if a == 1 {
                // return None;
                //(x + d + c, x + c) -> (x + d + c, d + c) + x = dk
                let end_out = AVarSum::constant(n);
                // add x = dk to map
                var_chain_map
                  .add_static(var, AffineVar { n: 0, a: decrease_amt, var: chaining_var });
                Some((start, end_out))
              } else {
                println!("tried to endchain {} into {} and couldn't #5", start, end);
                None
              }
            }
          }
          Err(_) => {
            println!("tried to endchain {} into {} and couldn't #6", start, end);
            None
          }
        }
      }
    }
  }
}

pub fn chain_side<S: TapeSymbol>(
  start: &[(S, AffineVar)],
  end: &[(S, AVarSum)],
  chaining_var: Var,
  var_chain_map: &mut VarChainMap,
) -> Option<(Vec<(S, AffineVar)>, Vec<(S, AVarSum)>)> {
  if start.len().abs_diff(end.len()) > 1 {
    return None;
  }
  let s_len: i32 = start.len().try_into().unwrap();
  let e_len: i32 = end.len().try_into().unwrap();

  let (mut start_out, mut end_out, start_slice, end_slice) = match s_len - e_len {
    1 => {
      let (start_s, start_avar) = start[0];
      (
        vec![(start_s, start_avar.times_var(chaining_var)?)],
        vec![],
        1,
        0,
      )
    }
    0 => (vec![], vec![], 0, 0),
    -1 => {
      let (end_s, end_avarsum) = &end[0];
      (
        vec![],
        vec![(*end_s, end_avarsum.times_var(chaining_var)?)],
        0,
        1,
      )
    }
    _ => unreachable!("checked abs diff above"),
  };

  for (i, (&(s_sym, s_var), (e_sym, e_var))) in
    zip_eq(start[start_slice..].iter(), end[end_slice..].iter()).enumerate()
  {
    if s_sym != *e_sym {
      return None;
    }
    let (s_var_out, e_var_out) = if i == 0 && start_slice == 0 && end_slice == 0 {
      chain_var_end(var_chain_map, s_var, e_var, chaining_var)?
    } else {
      chain_var(var_chain_map, s_var, e_var, chaining_var)?
    };
    start_out.push((s_sym, s_var_out));
    end_out.push((*e_sym, e_var_out));
  }
  Some((start_out, end_out))
}

pub fn chain_rule<P: Phase, S: TapeSymbol>(
  rule @ Rule {
    start:
      Config {
        state: state_start,
        left: left_start,
        head: head_start,
        right: right_start,
      },
    end:
      Config {
        state: state_end,
        left: left_end,
        head: head_end,
        right: right_end,
      },
  }: &Rule<P, S>,
) -> Option<Rule<P, S>> {
  // we're going to match the start to the end
  // and then have to deal with all the ends in a nasty way
  if state_start != state_end {
    return None;
  }
  if head_start != head_end {
    return None;
  }
  let chaining_var: Var = get_newest_var(&rule);
  let mut var_chain_map = VarChainMap::new();
  let (mut left_start_out, mut left_end_out) =
    chain_side(left_start, left_end, chaining_var, &mut var_chain_map)?;
  let (mut right_start_out, mut right_end_out) =
    chain_side(right_start, right_end, chaining_var, &mut var_chain_map)?;
  let static_hm = var_chain_map.static_hm;
  left_start_out = left_start_out
    .into_iter()
    .map(|(s, avar)| (s, avar.sub_equations(&static_hm)))
    .collect();
  right_start_out = right_start_out
    .into_iter()
    .map(|(s, avar)| (s, avar.sub_equations(&static_hm)))
    .collect();
  left_end_out = left_end_out
    .into_iter()
    .map(|(s, avarsum)| (s, avarsum.sub_equations(&static_hm)))
    .collect();
  right_end_out = right_end_out
    .into_iter()
    .map(|(s, avarsum)| (s, avarsum.sub_equations(&static_hm)))
    .collect();
  let ans = Some(Rule {
    start: Config {
      state: *state_start,
      left: left_start_out,
      head: *head_start,
      right: right_start_out,
    },
    end: Config {
      state: *state_start,
      left: left_end_out,
      head: *head_start,
      right: right_end_out,
    },
  });
  if static_hm.len() > 1 {
    println!(
      "exciting! chained\n{}\ninto\n{}\n",
      rule,
      ans.clone().unwrap()
    );
  }
  ans
}

fn set_var_to_repeat(
  var_chain_map: &mut VarChainMap,
  start: AffineVar,
  end: &AVarSum,
  chaining_var: Var,
) -> Option<()> {
  /*
  internal hm is like, when you chain (F, x) to (F, x+1), you have set x = x+1
  so you couldn't somewhere else set x = x+2
  external hm is like, when you chain (F, x) to (F, 3), you have set x = 3
  so not only can x not be anything except 3 anywhere else, you sub 3 for x everywhere else
  internal / external => changing / static
   */
  match start {
    AffineVar { n, a: 0, var: _var } => {
      if end.var_map.is_empty() {
        if n == end.n {
          Some(())
        } else {
          None
        }
      } else {
        match end.var_map.iter().exactly_one() {
          Ok((&end_var, &end_a)) => {
            let int_match = n.checked_sub(end.n)?;
            if int_match > 0 && int_match % end_a == 0 {
              var_chain_map.add_static(end_var, (int_match / end_a).into())
            } else {
              None
            }
          }
          Err(_) => {
            println!("tried to repeat {} into {} and couldn't #1", start, end);
            return None;
          }
        }
      }
    }
    AffineVar { n, a, var } => {
      if end.var_map.is_empty() {
        let int_match = end.n.checked_sub(n)?;
        if int_match > 0 && int_match % a == 0 {
          var_chain_map.add_static(var, (int_match / a).into())
        } else {
          None
        }
      } else {
        match end.var_map.iter().exactly_one() {
          Ok((&end_var, &b)) => {
            if var != end_var {
              println!("tried to repeat {} into {} and couldn't #2", start, end);
              return None;
            }
            // when we match ax + n to by + m we learn the internal fact
            // x -> (b/a)y + (m-n)/a
            let diff: i32 = i32::try_from(end.n).unwrap() - i32::try_from(n).unwrap();
            let b_i32: i32 = i32::try_from(b).unwrap();
            let a_i32 = i32::try_from(a).unwrap();
            if diff % a_i32 != 0 || b_i32 % a_i32 != 0 {
              return None;
            }
            var_chain_map.add_changing(var, SymbolVar { n: (diff / a_i32), a: (b / a), var })?;
            if n <= end.n {
              return Some(());
            }

            if n <= end.n {
              Some(())
            } else {
              if a > 1 {
                println!("chain {} into {}!", start, end);
              }
              let decrease_amt = n - end.n;
              if a == decrease_amt {
                /* (ax + n, ax + m), a = n - m,
                   (ax + m + a, ax + m) chains to
                   (ax + n, n) & k = x
                */
                // add k = x to map
                var_chain_map.add_static(chaining_var, AffineVar { n: 0, a: 1, var: start.var })
              } else if a == 1 {
                //(x + d + c, x + c) -> (x + d + c, d + c) + x = dk
                // add x = dk to map
                var_chain_map
                  .add_static(var, AffineVar { n: 0, a: decrease_amt, var: chaining_var })
              } else {
                println!("tried to repeat {} into {} and couldn't #3", start, end);
                None
              }
            }
          }
          Err(_) => {
            // println!("tried to repeat {} into {} and couldn't #4", start, end);
            None
          }
        }
      }
    }
  }
}

pub fn set_end_var_to_repeat(
  var_chain_map: &mut VarChainMap,
  start: AffineVar,
  end: &AVarSum,
  chaining_var: Var,
) -> Option<()> {
  /*
  (x, 3) -> lower bound x to 3 (or x -> y+3) then (3+y, 3) -> (3+yk, 3)
  (x, y) -> lower bound x to y and y to x ??

   */
  match start {
    AffineVar { n, a: 0, var: _var } => {
      if end.var_map.is_empty() {
        Some(())
      } else {
        match end.var_map.iter().exactly_one() {
          Ok((&end_var, &end_a)) => {
            //(2, 3+x)
            if n <= end.n {
              Some(())
            } else {
              // (3, 2+x)
              // lower bound end_a * end_var to n - end.n

              let rem = n - end.n;
              let lb = rem.div_ceil(end_a);
              var_chain_map.lower_bound(end_var, lb)
            }
          }
          Err(_) => {
            println!("tried to endrepeat {} into {} and couldn't #1", start, end);
            None
          }
        }
      }
    }
    AffineVar { n, a, var } => {
      if end.var_map.is_empty() {
        if end.n <= n {
          Some(())
        } else {
          // lower bound a * var to end.n - n
          let rem = end.n - n;
          let lb = rem.div_ceil(a);
          var_chain_map.lower_bound(var, lb)
        }
      } else {
        match end.var_map.iter().exactly_one() {
          Ok((&end_var, &b)) => {
            if var != end_var {
              println!("tried to endrepeat {} into {} and couldn't #2", start, end);
              return None;
            }
            // when we match ax + n to by + m we learn the internal fact
            // x -> (b/a)y + (m-n)/a
            let diff: i32 = i32::try_from(end.n).unwrap() - i32::try_from(n).unwrap();
            let b_i32: i32 = i32::try_from(b).unwrap();
            let a_i32 = i32::try_from(a).unwrap();
            if diff % a_i32 != 0 || b_i32 % a_i32 != 0 {
              return None;
            }
            var_chain_map.add_changing(var, SymbolVar { n: (diff / a_i32), a: (b / a), var })?;
            if n <= end.n {
              return Some(());
            }

            if n <= end.n {
              Some(())
            } else {
              if a > 1 {
                println!("chain {} into {}!", start, end);
              }
              let decrease_amt = n - end.n;
              if a == decrease_amt {
                /* (ax + n, ax + m), a = n - m,
                   (ax + m + a, ax + m) chains to
                   (ax + n, n) & k = x
                */
                // add k = x to map
                var_chain_map.add_static(chaining_var, AffineVar { n: 0, a: 1, var: start.var })
              } else if a == 1 {
                //(x + d + c, x + c) -> (x + d + c, d + c) + x = dk
                // add x = dk to map
                var_chain_map
                  .add_static(var, AffineVar { n: 0, a: decrease_amt, var: chaining_var })
              } else {
                println!("tried to endrepeat {} into {} and couldn't #3", start, end);
                None
              }
            }
          }
          Err(_) => {
            // println!("tried to endrepeat {} into {} and couldn't #4", start, end);
            None
          }
        }
      }
    }
  }
}

fn side_is_repeatable<S: TapeSymbol>(
  start: &[(S, AffineVar)],
  end: &[(S, AVarSum)],
  chaining_var: Var,
  var_chain_map: &mut VarChainMap,
) -> Option<()> {
  let s_len = start.len();
  let e_len = end.len();

  let (start_slice, end_slice) = match s_len.cmp(&e_len) {
    Less => (0, e_len - s_len),
    Equal => (0, 0),
    Greater => {
      if s_len == e_len + 1 && start[0].0 == S::empty() {
        (1, 0)
      } else {
        return None;
      }
    }
  };

  for (i, (&(s_sym, s_var), (e_sym, e_var))) in
    zip_eq(start[start_slice..].iter(), end[end_slice..].iter()).enumerate()
  {
    if s_sym != *e_sym {
      return None;
    }
    if i == 0 && start_slice == 0 && end_slice == 0 && s_sym == S::empty() {
      set_end_var_to_repeat(var_chain_map, s_var, e_var, chaining_var)?;
    } else {
      set_var_to_repeat(var_chain_map, s_var, e_var, chaining_var)?;
    };
  }
  Some(())
}

pub fn rule_runs_forever_if_consumes_all<P: Phase, S: TapeSymbol>(
  rule @ Rule {
    start:
      Config {
        state: state_start,
        left: left_start,
        head: head_start,
        right: right_start,
      },
    end:
      Config {
        state: state_end,
        left: left_end,
        head: head_end,
        right: right_end,
      },
  }: &Rule<P, S>,
) -> bool {
  /*
  this is sort of a lightweight or bad verson of chaining
  where we're essentially detecting that the rule is chainable
  but it may be the case that the chained version of the rule is not
  representable in our program, such as:
    phase: B  (F, 0 + 2*x_1) (T, 1 + 2*x_1) |>F<| (F, 3 + 2*x_1)
    into:
    phase: B  (T, 1 + 6*x_1) |>F<| (F, 3)

  criteria: start needs to match end, except end can spit something out, and start
  can consume extra empty symbols only from the end of the tape
   */
  if state_start != state_end {
    return false;
  }
  if head_start != head_end {
    return false;
  }
  let chaining_var: Var = get_newest_var(&rule);
  let mut var_chain_map = VarChainMap::new();

  let left_repeatable = side_is_repeatable(left_start, left_end, chaining_var, &mut var_chain_map);
  let right_repeatable =
    side_is_repeatable(right_start, right_end, chaining_var, &mut var_chain_map);
  return left_repeatable.is_some() && right_repeatable.is_some();
}

#[cfg(test)]
mod test {

  use crate::{
    parse::{
      parse_avar, parse_avar_sum, parse_end_half_tape, parse_exact, parse_half_tape, parse_rule,
    },
    rules::av_to_avs,
    tape::TapeHalf,
    turing::{Bit, Dir},
  };

  use super::*;

  fn chain_var_driver(
    start: AffineVar,
    end: &AVarSum,
    start_out: AffineVar,
    end_out: AVarSum,
    chaining_var: Var,
    eqs: Vec<(Var, Option<AffineVar>)>,
  ) {
    let mut var_chain_map = VarChainMap::new();
    assert_eq!(
      chain_var(&mut var_chain_map, start, end, chaining_var),
      Some((start_out, end_out)),
      "left is actual chain result, right is the prescribed answer"
    );
    assert_eq!(
      var_chain_map.static_hm.len(),
      eqs.len(),
      "{} {} {:?}",
      start,
      end,
      var_chain_map
    );
    for (var, ans) in eqs {
      let map_res: Option<AffineVar> = var_chain_map.static_hm.get(&var).copied();
      assert_eq!(map_res, ans);
    }
  }

  fn chain_var_is_none_driver(start: AffineVar, end: &AVarSum, chaining_var: Var) {
    let mut var_chain_map = VarChainMap::new();
    assert_eq!(
      chain_var(&mut var_chain_map, start, end, chaining_var),
      None,
      "left is actual chain result, right is always None"
    );
    assert!(
      var_chain_map.changing_hm.is_empty() && var_chain_map.static_hm.is_empty(),
      "VCM was not empty: {:?}",
      var_chain_map
    );
  }

  #[test]
  fn chain_var_test() {
    let chaining_var = Var(0);
    //(3, 3) -> (3, 3)
    let av3 = AffineVar::constant(3);
    let avs3 = AVarSum::constant(3);
    chain_var_driver(av3, &avs3, av3, avs3.clone(), chaining_var, vec![]);

    //(3, x) -> (3, 3)
    let x = Var(1);
    let av_x = AffineVar { n: 0, a: 1, var: x };
    let avs_x = av_x.into();
    chain_var_driver(
      av3,
      &avs_x,
      av3,
      avs3.clone(),
      chaining_var,
      vec![(x, Some(3.into()))],
    );

    //(x, 3) -> (3, 3)
    chain_var_driver(
      av_x,
      &AVarSum::constant(3),
      av3,
      avs3.clone(),
      chaining_var,
      vec![(x, Some(3.into()))],
    );

    //(x, x+1) -> (x, x+k)
    let mut avs_x_plus_one = avs_x.clone();
    avs_x_plus_one.n = 1;
    let mut avs_x_plus_cv = avs_x.clone();
    avs_x_plus_cv.add_avar(AffineVar { n: 0, a: 1, var: chaining_var });
    chain_var_driver(
      av_x,
      &avs_x_plus_one,
      av_x,
      avs_x_plus_cv,
      chaining_var,
      vec![],
    );

    //(2x + 5, 2x+8) -> None!! Because LHS is always odd and RHS is always even
    let av_2x_plus_5 = AffineVar { n: 5, a: 2, var: x };
    let mut avs_2x_plus_8: AVarSum = av_2x_plus_5.into();
    avs_2x_plus_8.add_avar(AffineVar::constant(3));
    chain_var_is_none_driver(av_2x_plus_5, &avs_2x_plus_8, chaining_var);

    // (2x + 5, 2x + 7) -> (2x + 5, 2x + 5 + 2k)
    let mut avs_2x_plus_7: AVarSum = av_2x_plus_5.into();
    avs_2x_plus_7.add_avar(AffineVar::constant(2));
    let mut avs_2x_plus_5_plus_2k: AVarSum = av_2x_plus_5.into();
    avs_2x_plus_5_plus_2k.add_avar(AffineVar { n: 0, a: 2, var: chaining_var });
    chain_var_driver(
      av_2x_plus_5,
      &avs_2x_plus_7,
      av_2x_plus_5,
      avs_2x_plus_5_plus_2k,
      chaining_var,
      vec![],
    );

    /*
    decreasing vars
    (x+1, x) -> (x+1, 1) + x = k
    (2x + 1, 2x) -> cannot chain
    (2x + 2, 2x) -> (2x + 2, 2) + x = k
    if decrease amt is d and coeff of x is c
    we have to set x = prev_x + d / c
    so d mod c == 0 <-> d = nc

    if d == c then easy: (cx + c, cx) -> (cx + c, c) + x = k
    if d == nc for some n, then maybe x = nk?
    (cx + nc, cx) -> (cx + nc, nc) + x = nk
    which means actually (nck + nc, nc)

    applying general alg to (x+3, x)
    c' = 3 w/ n=3 m=1
    sub x -> 3y
    (3y + 3, 3y)
    chains to
    (3y + 3, 3) & k = y
    which doesn't seem like what we want, because the above applies with
    x != 0 mod 3 as well

    so for d == c and d | c we know what to do but for c | d we don't yet exactly

    any decrease by non-integer: give up
    (2x + 1, x) -> cannot chain
     */

    // (x+1, x) chains to (x+1, 1) and k = x
    let av_x_plus_one = AffineVar { n: 1, a: 1, var: x };
    chain_var_driver(
      av_x_plus_one,
      &avs_x,
      av_x_plus_one,
      1.into(),
      chaining_var,
      vec![(chaining_var, Some(av_x))],
    );

    // (3x+3, 3x+2) chains to None
    let start = parse_exact(parse_avar("3 + 3*x_0"));
    let end_in = parse_exact(parse_avar_sum("2 + 3*x_0"));
    chain_var_is_none_driver(start, &end_in, chaining_var);

    // (4x+2, 4x) chains to None
    let start = parse_exact(parse_avar("2 + 4*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 4*x_0"));
    chain_var_is_none_driver(start, &end_in, chaining_var);

    // (2x, 2x) chains to (2x, 2x)
    let start = parse_exact(parse_avar("0 + 2*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 2*x_0"));
    let end_out = parse_exact(parse_avar_sum("0 + 2*x_0"));
    chain_var_driver(start, &end_in, start, end_out, chaining_var, vec![]);

    // (2x, x) chains to None
    let start = parse_exact(parse_avar("0 + 2*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 1*x_0"));
    chain_var_is_none_driver(start, &end_in, chaining_var);
    /*
    if d == nc for some n, then maybe x = nk?
    (cx + nc, cx) -> (cx + nc, nc) + x = nk
    which means actually (nck + nc, nc)

    suppose c is 1 and d > 1, the above reduces to
    x = dk
    (x + d, x) -> (x + d, d) + x = dk
    and then actually (dk + d, d)
     */

    let chaining_var = Var(1);

    // (x+2, x) -> (x+2, 2) x = 2k (ie end is (2k+2, 2))
    let start = parse_exact(parse_avar("2 + 1*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 1*x_0"));
    let end_out = parse_exact(parse_avar_sum("2"));
    let x_ans = parse_exact(parse_avar("0 + 2*x_1"));
    chain_var_driver(
      start,
      &end_in,
      start,
      end_out,
      chaining_var,
      vec![(Var(0), Some(x_ans))],
    );

    // (x+4, x+1) -> (3k+4, 4) x = 3k
    let start = parse_exact(parse_avar("4 + 1*x_0"));
    let end_in = parse_exact(parse_avar_sum("1 + 1*x_0"));
    let end_out = parse_exact(parse_avar_sum("4"));
    let x_ans = parse_exact(parse_avar("0 + 3*x_1"));
    chain_var_driver(
      start,
      &end_in,
      start,
      end_out,
      chaining_var,
      vec![(Var(0), Some(x_ans))],
    );

    // (x+9, x+2) -> (7k+9, 9) x = 7k
    let start = parse_exact(parse_avar("9 + 1*x_0"));
    let end_in = parse_exact(parse_avar_sum("2 + 1*x_0"));
    let end_out = parse_exact(parse_avar_sum("9"));
    let x_ans = parse_exact(parse_avar("0 + 7*x_1"));
    chain_var_driver(
      start,
      &end_in,
      start,
      end_out,
      chaining_var,
      vec![(Var(0), Some(x_ans))],
    );
  }

  #[test]
  fn chain_side_test() {
    let mut var_chain_map = VarChainMap::new();
    // ([], []) -> same
    let start = vec![];
    let end = vec![];
    assert_eq!(
      chain_side::<Bit>(&start, &end, Var(0), &mut var_chain_map),
      Some((start, end))
    );

    // ([(F, 1)], []) -> ([(F, x)], [])
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(F, 1)");
    assert_eq!(start.len(), 1);
    let start_out = parse_half_tape("(F, 0 + 1*x_0)");
    assert_eq!(start_out.len(), 1);
    let end = vec![];
    assert_eq!(
      chain_side(&start, &end, Var(0), &mut var_chain_map),
      Some((start_out, end))
    );

    // ([], [(T, 1)]) -> ([], [(T, x)])
    let mut var_chain_map = VarChainMap::new();
    let start = vec![];
    let end = av_to_avs(parse_half_tape("(T, 1)"));
    let end_out = av_to_avs(parse_half_tape("(T, 0 + 1*x_0)"));
    assert_eq!(
      chain_side(&start, &end, Var(0), &mut var_chain_map),
      Some((start, end_out))
    );

    // ([(T, 3), (F, x+1), (T, 2)], '') -> ('', '')
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 2)");
    assert_eq!(start.len(), 3);
    let end = av_to_avs(start.clone());
    assert_eq!(
      chain_side(&start, &end, Var(0), &mut var_chain_map),
      Some((start, end))
    );

    // ([(T, 3), (F, x+1), (T, 1)], [(T, 3), (F, x+2), (T, 3)])
    // ([(T, 3), (F, x+1), (T, 1)], [(T, 3), (F, 1+x+k), (T, 1+2k)])
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 1)");
    assert_eq!(start.len(), 3);
    let end = av_to_avs(parse_half_tape("(T, 3) (F, 2 + 1*x_0) (T, 3)"));
    assert_eq!(end.len(), 3);
    let end_out = parse_end_half_tape("(T, 3) (F, 1 + 1*x_0 + 1*x_1) (T, 1 + 2*x_1)");
    let (start_ans, end_ans) = chain_side(&start, &end, Var(1), &mut var_chain_map).unwrap();
    println!(
      "1 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    // ([(T, 3), (F, x+1), (T, 2)], [(T, 3), (F, x+2), (T, 1)])
    // ([(T, 3), (F, x+1), (T, 1+k)], [(T, 3), (F, 1+x+k), (T, 1)])
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 2)");
    assert_eq!(start.len(), 3);
    let end = parse_end_half_tape("(T, 3) (F, 2 + 1*x_0) (T, 1)");
    assert_eq!(end.len(), 3);
    let start_out = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 1 + 1*x_1)");
    let end_out = parse_end_half_tape("(T, 3) (F, 1 + 1*x_0 + 1*x_1) (T, 1)");
    let (start_ans, end_ans) = chain_side(&start, &end, Var(1), &mut var_chain_map).unwrap();
    println!(
      "2 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start_out, end_out));

    // ([(F, 1), (T, 4)], [(F, 1), (T, 4), (F, 1)])
    // ([(F, 1), (T, 4)], [(F, 1), (T, 4), (F, x)])
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(F, 1) (T, 4)");
    assert_eq!(start.len(), 2);
    let end = parse_end_half_tape("(F, 1) (T, 4) (F, 1)");
    assert_eq!(end.len(), 3);
    let end_out = parse_end_half_tape("(F, 1) (T, 4) (F, 0 + 1*x_0)");
    let (start_ans, end_ans) = chain_side(&start, &end, Var(0), &mut var_chain_map).unwrap();
    println!(
      "3 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    // ([(F, 1), (T, 3)], [(F, 1), (T, 4), (F, 1)]) -> None
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(F, 1) (T, 3)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(F, 1) (T, 4) (F, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0), &mut var_chain_map), None);

    // ([(F, 1), (T, 4)], [(F, 1), (T, 3), (F, 1)]) -> None
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(F, 1) (T, 4)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(F, 1) (T, 3) (F, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0), &mut var_chain_map), None);

    // ([(T, 2), (F, 4)] [(T, 2), (F, 3), (T, 1)]) -> None
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(T, 2) (F, 4)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(T, 2) (F, 3) (T, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0), &mut var_chain_map), None);

    // ([(T, 2), (F, 3), (T, 1)] [(T, 2), (F, 4)]) -> None
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(T, 2) (F, 3) (T, 1)");
    let end = av_to_avs(parse_half_tape("(T, 2) (F, 4)"));
    assert_eq!(chain_side(&start, &end, Var(0), &mut var_chain_map), None);

    let chain_var = Var(1);
    // (F, 1) (T, 4) (F, x+1) -> (F, 1) (T, 4) (F, x)
    // (F, 1) (T, 4) (F, x+1) -> (F, 1) (T, 4) (F, 1)
    // k = x
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(F, 1) (T, 4) (F, 1 + 1*x_0)");
    let end = parse_end_half_tape("(F, 1) (T, 4) (F, 0 + 1*x_0)");
    let end_out = parse_end_half_tape("(F, 1) (T, 4) (F, 1)");
    let (start_ans, end_ans) = chain_side(&start, &end, chain_var, &mut var_chain_map).unwrap();
    println!(
      "4 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    let chain_var_rhs = AffineVar { n: 0, a: 1, var: Var(0) };
    assert_eq!(var_chain_map.static_hm.get(&Var(1)), Some(&chain_var_rhs));

    // (F, 1) (T, 4) (F, x+2) -> (F, 1) (T, 4) (F, x)
    // (F, 1) (T, 4) (F, x+2) -> (F, 1) (T, 4) (F, 2)
    // x = 2k
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(F, 1) (T, 4) (F, 2 + 1*x_0)");
    let end = parse_end_half_tape("(F, 1) (T, 4) (F, 0 + 1*x_0)");
    let end_out = parse_end_half_tape("(F, 1) (T, 4) (F, 2)");
    let (start_ans, end_ans) = chain_side(&start, &end, chain_var, &mut var_chain_map).unwrap();
    println!(
      "5 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    let x_0_rhs = AffineVar { n: 0, a: 2, var: chain_var };
    assert_eq!(var_chain_map.static_hm.get(&Var(0)), Some(&x_0_rhs));

    // (T, 4) (F, x+4) (T, 3) -> (T, 4) (F, x+1) (T, 3)
    // becomes
    // (T, 4) (F, x+4) (T, 3) -> (T, 4) (F, 4) (T, 3)
    // x = 3k
    let mut var_chain_map = VarChainMap::new();
    let start = parse_half_tape("(T, 4) (F, 4 + 1*x_0) (T, 3)");
    let end = parse_end_half_tape("(T, 4) (F, 1 + 1*x_0) (T, 3)");
    let end_out = parse_end_half_tape("(T, 4) (F, 4) (T, 3)");
    let (start_ans, end_ans) = chain_side(&start, &end, chain_var, &mut var_chain_map).unwrap();
    println!(
      "6 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    let x_0_rhs = AffineVar { n: 0, a: 3, var: chain_var };
    assert_eq!(var_chain_map.static_hm.get(&Var(0)), Some(&x_0_rhs));
  }

  #[test]
  fn chaining_rules_test() {
    /*
    phase: A  (F, 1) |>F<| (T, x) (F, 1)
    into:
    phase: A   |>F<| (T, 1 + x) (F, 1)

    chained n times:
    phase: A  (F, n) |>F<| (T, x) (F, 1)
    into:
    phase: A   |>F<| (T, n + x) (F, 1)

    chain (x, x+1) (x, x+n)

    chain (x+1, x) (x+n, x)
    no! instead
    chain (x+1, x) (x+1, 1) + x = n

     */
    let rule = parse_exact(parse_rule(
      "phase: A  (F, 1) |>F<| (T, 1 + 1*x_0) (F, 1)
into:
phase: A   |>F<| (T, 2 + 1*x_0) (F, 1)",
    ));
    let chained_rule = parse_exact(parse_rule(
      "phase: A  (F, 0 + 1*x_1) |>F<| (T, 1 + 1*x_0) (F, 1)
into:
phase: A   |>F<| (T, 1 + 1*x_0 + 1*x_1) (F, 1)",
    ));
    let ans = chain_rule(&rule).unwrap();
    println!("test 1: by chaining, obtained:\n{}", ans);
    assert_eq!(ans, chained_rule);
    let rule = parse_exact(parse_rule(
      "phase: B  (T, 1 + 1*x_0) (F, 1) |>F<| (T, 0 + 1*x_0)
into:
phase: B  (T, 0 + 1*x_0) (F, 1) |>F<| (T, 1 + 1*x_0)",
    ));
    //     let chained_rule = parse_exact(parse_rule(
    //       "phase: B  (T, 1 + 1*x_0) (F, 1) |>F<| (T, 0 + 1*x_0)
    // into:
    // phase: B  (T, 1) (F, 1) |>F<| (T, 0 + 2*x_0)",
    //     ));
    /* I had the above, but that is wrong!
    (T, 6) (F, 1) >F< (T, 5)
    <rule app>
    (T, 5) (F, 1) >F< (T, 6)
    rule no longer applies!!
     */
    let ans = chain_rule(&rule);
    if let Some(wrong_ans) = ans.clone() {
      println!("test 2: chained:\n{}\nand got\n{}", rule, wrong_ans);
    }
    assert_eq!(ans, None);

    let rule = parse_exact(parse_rule(
      "phase: C  (T, 2 + 1*x_0) |>T<| (T, 0 + 1*x_1)
into:
phase: C  (T, 0 + 1*x_0) |>T<| (T, 2 + 1*x_1)",
    ));
    let chained_rule = parse_exact(parse_rule(
      "phase: C  (T, 2 + 2*x_2) |>T<| (T, 0 + 1*x_1)
into:
phase: C  (T, 2) |>T<| (T, 0 + 1*x_1 + 2*x_2)",
    ));
    let ans = chain_rule(&rule).unwrap();
    println!("test 3: by chaining, obtained:\n{}", ans);
    assert_eq!(ans, chained_rule);

    let rule = parse_exact(parse_rule(
      "phase: B  (F, 1) |>F<| (T, 1 + 1*x_0) (F, 3 + 1*x_0)
into:
phase: B   |>F<| (T, 4 + 1*x_0) (F, 1 + 1*x_0)",
    ));
    /*example tape: (F, 3) |>F<| (T, 5) (F, 7)
    1 rule app (x_0 = 4)
    (F, 2) >F< (T, 8) (F, 5)
    now rule doesn't apply
    */
    let ans = chain_rule(&rule);
    assert_eq!(ans, None);

    let rule = parse_exact(parse_rule(
      "phase: B  (F, 1) |>F<| (T, 1 + 1*x_0) (F, 3 + 1*x_1)
into:
phase: B   |>F<| (T, 4 + 1*x_0) (F, 1 + 1*x_1)",
    ));
    let chain_var = get_newest_var(&rule);
    assert_eq!(chain_var, Var(2));
    /*example tape: (F, 3) |>F<| (T, 5) (F, 7)
    1 rule app (x_0 = 4, x_1 = 4)
    (F, 2) >F< (T, 8) (F, 5)
    1 rule app (x_0 = 7, x_1 = 2)
    (F, 1) >F< (T, 11) (F, 3)
    */
    //sub x_1 = 2*x_2 where x_2 is iter variable
    let chained_rule = parse_exact(parse_rule(
      "phase: B  (F, 0 + 1*x_2) |>F<| (T, 1 + 1*x_0) (F, 3 + 2*x_2)
into:
phase: B   |>F<| (T, 1 + 1*x_0 + 3*x_2) (F, 3)",
    ));
    println!("test 4: chaining:\n{}", rule);
    let ans = chain_rule(&rule).unwrap();
    println!("test 4: by chaining, obtained:\n{}", ans);
    assert_eq!(ans, chained_rule);

    let rule = parse_exact(parse_rule(
      "phase: B  (F, 1) (T, 0 + 1*x_0) |>F<| (T, 0 + 3*x_0)
into:
phase: B  (T, 0 + 1*x_0) |>F<| (T, 0 + 3*x_0) (F, 1)",
    ));
    /*
    (T, 5) >F< (T, 5)
    <rule app, x_0 = 5>
    (T, 11) >F< (T, 10)
    the goal of this test is to ensure that the fact that we set x_0 to
    2a + 1 on the left and 2a on the right conflict
    */
    let chained_rule = parse_exact(parse_rule(
      "phase: B  (F, 0 + 1*x_1) (T, 0 + 1*x_0) |>F<| (T, 0 + 3*x_0)
into:
phase: B  (T, 0 + 1*x_0) |>F<| (T, 0 + 3*x_0) (F, 0 + 1*x_1)",
    ));
    println!("test 5: chaining:\n{}", rule);
    let ans = chain_rule(&rule).unwrap();
    println!("test 5: by chaining, obtained:\n{}", ans);
    assert_eq!(ans, chained_rule);

    let rule = parse_exact(parse_rule(
      "phase: B  (F, 1) (T, 0 + 1*x_0) |>F<| (T, 0 + 3*x_0)
into:
phase: B  (T, 1 + 1*x_0) |>F<| (T, 0 + 3*x_0)",
    ));
    /*
    (T, 4) >F< (T, 12)
    <rule app, x_0 = 4>
    (T, 5) >F< (T, 12)
    the goal of this test is to ensure that the fact that we set x_0 to
    a + 1 on the left and a on the right conflict
    */
    let ans = chain_rule(&rule);
    if let Some(wrong_ans) = ans.clone() {
      println!("test 6: chained:\n{}\nand got\n{}", rule, wrong_ans);
    }
    assert_eq!(ans, None);

    let rule = parse_exact(parse_rule(
      "phase: B  (T, 1 + 1*x_0) (F, 1) |>F<| (T, 0 + 1*x_1)
into:
phase: B  (T, 0 + 1*x_0) (F, 1) |>F<| (T, 1 + 1*x_1)",
    ));
    let chained_rule = parse_exact(parse_rule(
      "phase: B  (T, 1 + 1*x_0) (F, 1) |>F<| (T, 0 + 1*x_1)
into:
phase: B  (T, 1) (F, 1) |>F<| (T, 0 + 1*x_1 + 1*x_0)",
    ));
    let ans = chain_rule(&rule).unwrap();
    println!("test 7: by chaining, obtained:\n{}", ans);
    assert_eq!(ans, chained_rule);
  }

  fn rule_runs_forever_if_consumes_all_driver(rule: &str, ans: bool) {
    let rule = parse_exact(parse_rule(rule));
    let runs_forever = rule_runs_forever_if_consumes_all(&rule);
    assert_eq!(
      runs_forever, ans,
      "rule that failed:\n{}\nans should have been {} but was {}",
      rule, ans, runs_forever
    );
  }

  #[test]
  fn test_rule_runs_forever_if_consumes_all() {
    /*
    examples:
    yes:
    */
    let rule_str = "phase: B  (F, 0 + 2*x_1) (T, 1 + 2*x_1) |>F<| (F, 3 + 2*x_1)
into:
phase: B  (T, 1 + 6*x_1) |>F<| (F, 3)";
    rule_runs_forever_if_consumes_all_driver(rule_str, true);

    let rule_str = "phase: B  (F, 0 + 2*x_1) (T, 1 + 2*x_1) |>F<| (F, 3)
into:
phase: B  (T, 3 + 2*x_1) |>F<| (F, 1 + 2*x_1)";
    rule_runs_forever_if_consumes_all_driver(rule_str, true);
    let rule_str = "phase: B  (T, 1 + 2*x_1) |>F<| (F, 3 + 2*x_1)
into:
phase: B  (T, 1 + 4*x_1) |>F<| (F, 3)";
    rule_runs_forever_if_consumes_all_driver(rule_str, true);

    let rule_str = "phase: B  (T, 1 + 2*x_1) |>F<| (F, 3 + 2*x_1)
into:
phase: B  (F, 1) (T, 1) (F, 1) (T, 1 + 4*x_1) |>F<| ";
    rule_runs_forever_if_consumes_all_driver(rule_str, true);
    // no:
    let rule_str = "phase: B  (F, 0 + 2*x_1) (T, 1 + 2*x_1) |>F<| (F, 3 + 2*x_1)
into:
phase: B  (T, 1 + 6*x_1) |>F<| (F, 1) (T, 1) (F, 1)";
    rule_runs_forever_if_consumes_all_driver(rule_str, false);

    let rule_str = "phase: B  (F, 0 + 2*x_1) (T, 1 + 2*x_1) |>F<| (T, 3 + 2*x_1)
into:
phase: B  (T, 1 + 6*x_1) |>F<| (T, 3)";
    rule_runs_forever_if_consumes_all_driver(rule_str, false);
    let rule_str = "phase: B  (F, 0 + 2*x_1) (T, 1 + 2*x_1) |>F<| (F, 1) (T, 1) (F, 1)
into:
phase: B  (T, 1 + 4*x_1) |>F<| (T, 3)";
    rule_runs_forever_if_consumes_all_driver(rule_str, false);
    let rule_str = "phase: B  (F, 0 + 2*x_1) (T, 1 + 2*x_1) |>F<| (T, 3) (F, 3)
into:
phase: B  (T, 1 + 4*x_1) |>F<| (T, 6)";
    rule_runs_forever_if_consumes_all_driver(rule_str, false);
  }
}
