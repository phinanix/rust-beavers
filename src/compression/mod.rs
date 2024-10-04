use either::Either::{self, Left, Right};
use itertools::{zip_eq, Itertools};
use proptest::test_runner::Config;
use smallvec::{smallvec, SmallVec};
use std::{
  cmp::{max_by_key, Ordering::*},
  collections::{HashMap, HashSet},
  fmt::{Debug, Display, Pointer, Write},
  hash::Hash,
  ops::{Add, AddAssign},
};

use crate::{
  brady::get_rs_hist_for_machine,
  chain::{chain_var, sub_equations_vec, VarChainMap},
  rules::{add_vars_to_set, AVarSum, AffineVar, SymbolVar, Var},
  tape::ExpTape,
  turing::{Bit, Edge, Phase, SmallBinMachine, State, TapeSymbol, Trans, Turing, AB},
  Dir,
};

// type TransHist<P,S> = Vec<(u32, P, S)>;

pub fn history_to_trans_history<P: Phase, S: TapeSymbol>(
  hist: &[(u32, P, ExpTape<S, u32>)],
) -> Vec<(u32, P, S)> {
  hist
    .iter()
    .map(|&(steps, p, ExpTape { head, .. })| (steps, p, head))
    .collect_vec()
}

/*
  returns:
  Left: the step at which the machine was infinite
  or
  Right:
   the transition history, which is a
   Vec<(u32, P, S)> which is (steps, phase, symbol)
*/
pub fn get_transition_hist_for_machine<P: Phase, S: TapeSymbol>(
  machine: &impl Turing<P, S>,
  num_steps: u32,
  verbose: bool,
) -> Either<u32, Vec<(u32, P, S)>> {
  let (hist, _rs_hist) = match get_rs_hist_for_machine(machine, num_steps, verbose) {
    Left(s) => return Left(s),
    Right((hist, rs_hist)) => (hist, rs_hist),
  };
  Right(history_to_trans_history(&hist))
}

pub fn assert_step_size_one<P, S>(trans_hist: &[(u32, P, S)]) {
  let mut prev_step = trans_hist[0].0;
  for &(step, _, _) in &trans_hist[1..] {
    let diff = step - prev_step;
    assert_eq!(diff, 1, "step size one {} {}", step, prev_step);
    prev_step = step;
  }
}

fn display_trans<P: Phase>(phase: P, bit: Bit) -> char {
  let phase_byte = phase.as_byte();
  let phase_letter = AB.chars().nth(phase_byte as usize).unwrap();
  if bit.0 {
    phase_letter.to_ascii_uppercase()
  } else {
    phase_letter.to_ascii_lowercase()
  }
}

fn display_trans_group<P: Phase>(group: &Group<(P, Bit)>) -> String {
  let mut group_str = String::new();
  for &(phase, bit) in group.0.iter() {
    group_str.push(display_trans(phase, bit));
  }
  group_str
}

fn display_trans_rle_group<P: Phase>(group: &Group<(P, Bit)>, len: u32) -> String {
  let group_str = display_trans_group(group);
  if len == 1 {
    group_str
  } else {
    format!(" ({}, {}) ", group_str, len)
  }
}

fn display_char_group(group: &Group<char>, len: u32) -> String {
  let mut group_str = String::new();
  for &c in group.0.iter() {
    group_str.push(c);
  }
  if len == 1 {
    group_str
  } else {
    format!(" ({}, {}) ", group_str, len)
  }
}

fn display_group_gen<T: Display>(group: &Group<T>, len: u32) -> String {
  let mut group_str = String::new();
  for c in group.0.iter() {
    group_str.push_str(&c.to_string());
  }
  if len == 1 {
    group_str
  } else {
    format!(" ({}, {}) ", group_str, len)
  }
}

fn display_rle_gen<T: Display>(t: T, len: u32) -> String {
  if len == 1 {
    t.to_string()
  } else {
    format!(" ({}, {}) ", t.to_string(), len)
  }
}

fn display_maybe_rle<P: Phase>(mb_rle: &Either<(P, Bit), (Group<(P, Bit)>, u32)>) -> String {
  match mb_rle {
    Left((p, b)) => display_trans(*p, *b).to_string(),
    Right((g, len)) => display_trans_rle_group(g, *len),
  }
}

fn display_maybe_rle_char(mb_rle: &Either<char, (String, u32)>) -> String {
  match mb_rle {
    Left(c) => c.to_string(),
    Right((s, n)) => display_stringnum(s.clone(), *n),
  }
}

fn display_maybe_rle_gen<S: Display, T: Display>(mb_rle: &Either<S, (Group<T>, u32)>) -> String {
  match mb_rle {
    Left(t) => t.to_string(),
    Right((group, len)) => display_group_gen(group, *len),
  }
}

pub fn display_trans_hist<P: Phase>(trans_hist: &[(P, Bit)]) -> String {
  trans_hist
    .iter()
    .map(|&(p, b)| display_trans(p, b))
    .collect()
}

pub fn display_grouped_trans_hist<P: Phase>(trans_hist: &[(Group<(P, Bit)>, u32)]) -> String {
  trans_hist
    .iter()
    .map(|(g, num)| display_trans_rle_group(g, *num))
    .collect()
}

pub fn display_rle_hist_gen<T: Display>(rle_hist: &[(T, u32)]) -> String {
  rle_hist
    .iter()
    .map(|(t, len)| display_rle_gen(t, *len))
    .collect()
}

pub fn display_stringnum(s: String, n: u32) -> String {
  format!(" ({}, {}) ", s, n)
}

pub fn display_mb_rule<P: Phase>(mb_rule: &Either<(P, Bit), (String, u32)>) -> String {
  match mb_rule {
    Left((p, b)) => display_trans(*p, *b).to_string(),
    Right((s, n)) => display_stringnum(s.clone(), *n),
  }
}

pub fn display_partial_rle_hist<P: Phase>(
  partial_rle_hist: &[Either<(P, Bit), (String, u32)>],
) -> String {
  partial_rle_hist
    .iter()
    .map(|i| display_mb_rule(i))
    .collect()
}

pub fn display_partial_rle_str(partial_rle_hist: &[Either<char, (String, u32)>]) -> String {
  partial_rle_hist
    .iter()
    .map(|i| display_maybe_rle_char(i))
    .collect()
}

pub fn display_two_group_rle<P: Phase>(
  two_group_rle_hist: &[Either<(Group<(P, Bit)>, u32), (String, u32)>],
) -> String {
  two_group_rle_hist
    .iter()
    .map(|lr| match lr {
      Left((g, num)) => display_trans_rle_group(g, *num),
      Right((s, num)) => {
        format!(" *({}, {}) ", s, num)
      }
    })
    .collect()
}

pub fn display_two_chargroup_rle(
  two_chargroup_rle: &[Either<(Group<char>, u32), (Group<char>, u32)>],
) -> String {
  two_chargroup_rle
    .iter()
    .map(|lr| match lr {
      Left((g, num)) => display_char_group(g, *num),
      Right((g, num)) => {
        let mut partial_ans = display_char_group(g, *num);
        partial_ans = partial_ans.split_off(1);
        format!(" *{}", partial_ans)
      }
    })
    .collect()
}

// pub fn display_partial_rle_gen<S: Display, T: Display>(partial_rle_hist: &[Either<S, (Group<T>, u32)>]) -> String {
//   partial_rle_hist.iter().map(|i|display_maybe_rle_gen(i)).collect()
// }

// pub fn display
pub fn push_rle<T: Eq, C: AddAssign + From<u32>>(stack: &mut Vec<(T, C)>, item: T) {
  match stack.last_mut() {
    None => {
      stack.push((item, 1.into()));
    }
    Some((t, count)) => {
      if item == *t {
        *count += 1.into();
      } else {
        stack.push((item, 1.into()));
      }
    }
  }
}

pub fn append_rle<S: Eq + Clone, T: Add<Output = T> + Clone>(
  stack: &mut Vec<(S, T)>,
  items: &[(S, T)],
) {
  match stack.last_mut() {
    None => {
      for item in items {
        stack.push(item.clone());
      }
    }
    Some((s_last, t_last)) => {
      if !items.is_empty() {
        let (s_first, t_first) = items[0].clone();
        if s_first == *s_last {
          *t_last = t_last.clone() + t_first;
        } else {
          stack.push((s_first, t_first));
        }
        for item in &items[1..] {
          stack.push(item.clone());
        }
      }
    }
  }
}

pub fn rle_encode<T: Eq + Clone>(seq: &[T]) -> Vec<(T, u32)> {
  let mut out = vec![];
  for item in seq {
    push_rle(&mut out, item.clone());
  }
  out
}

pub fn push_partial_rle<T: Eq, R>(
  stack: &mut Vec<Either<(T, u32), R>>,
  item_or_group: Either<T, R>,
) {
  let item = match item_or_group {
    Left(t) => t,
    Right(group) => {
      stack.push(Right(group));
      return;
    }
  };
  match stack.last_mut() {
    None => {
      stack.push(Left((item, 1)));
    }
    Some(Right(_)) => {
      stack.push(Left((item, 1)));
    }
    Some(Left((t, count))) => {
      if item == *t {
        *count += 1;
      } else {
        stack.push(Left((item, 1)));
      }
    }
  }
}

// the lefts are new, the rights were there already
pub fn rle_partial_rle<T: Eq + Clone, R: Clone>(seq: &[Either<T, R>]) -> Vec<Either<(T, u32), R>> {
  let mut out = vec![];
  for item in seq {
    push_partial_rle(&mut out, item.clone());
  }
  out
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Group<T>(SmallVec<[T; 10]>);

impl<T: Display> Display for Group<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for t in self.0.iter() {
      f.write_str(&t.to_string())?
    }
    Ok(())
  }
}

// drops elements at the end of the vec if there aren't enough to fill a group
pub fn group_vec<T: Debug + Copy>(seq: &[T], group_size: u32) -> Vec<Group<T>> {
  let mut out = vec![];
  let mut cur_group = Group(smallvec![]);
  let mut cur_group_len = 0;
  for &item in seq {
    // dbg!(&cur_group, cur_group_len);
    cur_group.0.push(item);
    cur_group_len += 1;
    if cur_group_len == group_size {
      out.push(cur_group);
      cur_group = Group(smallvec![]);
      cur_group_len = 0;
    }
  }
  out
}

pub fn group_any<T: Clone>(seq: &[T], group_size: u32) -> Vec<Group<T>> {
  let mut out = vec![];
  let mut cur_group = Group(smallvec![]);
  let mut cur_group_len = 0;
  for item in seq {
    cur_group.0.push(item.clone());
    cur_group_len += 1;
    if cur_group_len == group_size {
      out.push(cur_group);
      cur_group = Group(smallvec![]);
      cur_group_len = 0;
    }
  }
  out.push(cur_group);
  out
}

pub fn group_partial_rle<T: Debug + Copy, R: Clone>(
  seq: &[Either<T, R>],
  group_size: u32,
) -> Vec<Either<Group<T>, R>> {
  let mut out = vec![];
  let mut cur_group = Group(smallvec![]);
  let mut cur_group_len = 0;
  for item in seq {
    match item {
      Left(t) => {
        cur_group.0.push(*t);
        cur_group_len += 1;
        if cur_group_len == group_size {
          out.push(Left(cur_group));
          cur_group = Group(smallvec![]);
          cur_group_len = 0;
        }
      }
      Right(gl) => {
        out.push(Left(cur_group));
        cur_group = Group(smallvec![]);
        cur_group_len = 0;

        out.push(Right(gl.clone()));
      }
    }
  }
  out.push(Left(cur_group));
  out
}

pub fn first_diff<T: Debug + Eq + Clone + Copy>(subseq: &Group<T>, offset: usize) -> usize {
  // for idx in offset..subseq.0.len()
  for idx in 0..subseq.0.len() - offset {
    if subseq.0[idx] != subseq.0[idx + offset] {
      return idx;
    }
  }
  subseq.0.len() - offset
}

pub fn calc_letter_prefix<T: Debug + Eq + Clone + Copy>(
  subseq: &Group<T>,
  valid_shortenings: &Vec<Vec<usize>>,
  t: T,
  prefix_len: usize,
) -> usize {
  if subseq.0[prefix_len] == t {
    return prefix_len + 1;
  } else {
    for &shorter_len in valid_shortenings[prefix_len].iter() {
      if subseq.0[shorter_len] == t {
        return shorter_len + 1;
      }
    }
    return 0;
  }
}

pub fn preprocess_subseq<T: Debug + Eq + Clone + Copy + Hash>(
  subseq: &Group<T>,
) -> HashMap<(T, usize), usize> {
  let mut valid_shortenings = vec![];
  for _idx in 0..=subseq.0.len() {
    valid_shortenings.push(vec![]);
  }
  for offset in 1..subseq.0.len() {
    let first_diff = first_diff(subseq, offset);
    for prefix_len in 0..=first_diff {
      valid_shortenings[prefix_len + offset].push(prefix_len);
    }
  }

  let mut all_ts = HashSet::new();
  for &t in subseq.0.iter() {
    all_ts.insert(t);
  }

  let mut table: HashMap<(T, usize), usize> = HashMap::new();
  for &t in all_ts.iter() {
    for prefix_len in 0..subseq.0.len() {
      let ans = calc_letter_prefix(&subseq, &valid_shortenings, t, prefix_len);
      table.insert((t, prefix_len), ans);
    }
  }
  table
}

pub fn rle_specific_subseq<T: Debug + Eq + Clone + Copy + Hash>(
  seq: &[Either<T, (String, u32)>],
  subseq: &Group<T>,
  subseq_str: &str,
) -> Vec<Either<T, (String, u32)>> {
  let table: HashMap<(T, usize), usize> = preprocess_subseq(subseq);
  let min_group_count = 3;

  let mut idx_in_group: usize = 0;
  let mut group_count = 0;
  let mut out: Vec<Either<T, (String, u32)>> = vec![];

  // invariant: inp_so_far = out+(subseq, group_count)+subseq[:idx_in_group]
  for item in seq {
    match item {
      Left(t) => {
        let new_idx_in_group = *table.get(&(*t, idx_in_group)).unwrap_or(&0);
        // .unwrap_or_else(|| panic!("t {:?} idx_in_group {} subseq {:?}\nseq {:?}",
        // t, idx_in_group, subseq, seq));

        if new_idx_in_group <= idx_in_group && new_idx_in_group > 0 {
          if group_count >= min_group_count {
            out.push(Right((subseq_str.to_owned(), group_count)));
          } else {
            for _ in 0..group_count {
              out.extend(subseq.0.iter().map(|&t| Left(t)))
            }
          }
          group_count = 0;

          let diff = idx_in_group - new_idx_in_group;
          for group_idx in 0..=diff {
            out.push(Left(subseq.0[group_idx]));
          }
          idx_in_group = new_idx_in_group;
        } else if new_idx_in_group == subseq.0.len() {
          group_count += 1;
          idx_in_group = 0;
        } else if new_idx_in_group == idx_in_group + 1 {
          idx_in_group = new_idx_in_group;
        } else {
          assert_eq!(new_idx_in_group, 0);

          if group_count > 0 {
            if group_count >= min_group_count {
              out.push(Right((subseq_str.to_owned(), group_count)));
            } else {
              for _ in 0..group_count {
                out.extend(subseq.0.iter().map(|&t| Left(t)))
              }
            }
            group_count = 0;
          }
          assert_eq!(group_count, 0);

          let diff = idx_in_group - new_idx_in_group;
          for group_idx in 0..diff {
            out.push(Left(subseq.0[group_idx]));
          }
          idx_in_group = new_idx_in_group;

          out.push(Left(*t));
        }
      }
      Right(grp) => {
        // we need to flush everything into the output buffer here

        if group_count >= min_group_count {
          out.push(Right((subseq_str.to_owned(), group_count)));
        } else {
          for _ in 0..group_count {
            out.extend(subseq.0.iter().map(|&t| Left(t)))
          }
        }
        group_count = 0;

        for group_idx in 0..idx_in_group {
          out.push(Left(subseq.0[group_idx]));
        }
        idx_in_group = 0;

        out.push(Right(grp.clone()));
      }
    }
    // dbg!(item, idx_in_group, group_count);
    // dbg!(&out);
    // println!();
  }
  // we need to flush everything into the output buffer here
  // this is copied from the case "right" above
  if group_count >= min_group_count {
    out.push(Right((subseq_str.to_owned(), group_count)));
  } else {
    for _ in 0..group_count {
      out.extend(subseq.0.iter().map(|&t| Left(t)))
    }
  }
  // group_count = 0;

  for group_idx in 0..idx_in_group {
    out.push(Left(subseq.0[group_idx]));
  }
  // idx_in_group = 0;

  out
}

pub fn rle_specific_subseq_old<T: Debug + Eq + Clone + Copy>(
  seq: &[Either<T, (Group<T>, u32)>],
  subseq: &Group<T>,
) -> Vec<Either<T, (Group<T>, u32)>> {
  let min_group_count = 3;

  // let target = &subseq.0;
  let mut idx_in_group = 0;
  let mut group_count = 0;
  let mut out: Vec<Either<T, (Group<T>, u32)>> = vec![];
  let mut backlog = vec![];
  for item in seq {
    match item {
      Left(t) if t == &subseq.0[idx_in_group] => {
        // we'll provisionally proceed to start making this into a group
        // but we have to be able to unwind that if we fail, so note t
        // into our backlog
        backlog.push(t);
        idx_in_group += 1;
        if idx_in_group == subseq.0.len() {
          idx_in_group = 0;
          group_count += 1;
          if group_count >= min_group_count {
            // once we're above the min_group_count, we can clear the backlog
            // when we finish a group, as we will in fact store the whole
            // group at that point
            backlog = vec![];
          }
        }
      }
      not_extendable => {
        // we need to flush everything into the output buffer here
        if group_count >= min_group_count {
          out.push(Right((subseq.clone(), group_count)));
        }
        out.extend(backlog.into_iter().map(|t| Left(*t)));
        idx_in_group = 0;
        group_count = 0;
        backlog = vec![];
        // and now put in not_extendable itself
        if let Left(t) = not_extendable
          && t == &subseq.0[idx_in_group]
        {
          // note this is copied from above
          backlog.push(t);
          idx_in_group += 1;
          if idx_in_group == subseq.0.len() {
            idx_in_group = 0;
            group_count += 1;
            if group_count >= min_group_count {
              // once we're above the min_group_count, we can clear the backlog
              // when we finish a group, as we will in fact store the whole
              // group at that point
              backlog = vec![];
            }
          }
        } else {
          out.push(not_extendable.clone());
        }
      }
    }
    // dbg!(item, idx_in_group, group_count);
    // println!();
  }
  // we need to flush everything into the output buffer here
  if group_count >= min_group_count {
    out.push(Right((subseq.clone(), group_count)));
  }
  out.extend(backlog.into_iter().map(|t| Left(*t)));
  out
}

pub fn select_next_subseq<T: Clone, R: Clone>(grouped_rle: &[Either<(T, u32), R>]) -> Option<T> {
  let min_repeat_len = 5;
  grouped_rle
    .iter()
    .filter_map(|e| e.clone().left().filter(|(_, n)| *n >= min_repeat_len))
    .max_by_key(|(_, n)| *n)
    .map(|(t, _)| t)
}

// much like Tape / ExpTape, the *last* thing in the Vec is the closest to the head,
// for both left and right
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CConfig<P, S, V> {
  pub state: P,
  pub left: Vec<(S, V)>,
  pub head: S,
  pub right: Vec<(S, V)>,
}

impl<P: Display, S: Display, V: Display> Display for CConfig<P, S, V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "phase: {}  ", self.state)?;
    for (s, v) in self.left.iter() {
      write!(f, "({}, {}) ", s, v)?;
    }
    if self.left.is_empty() {
      write!(f, " ")?;
    }
    write!(f, "|>{}<|", self.head)?;
    if self.right.is_empty() {
      write!(f, " ")?;
    }
    for (s, v) in self.right.iter().rev() {
      write!(f, " ({}, {})", s, v)?;
    }
    Ok(())
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum RuleEnd<P, S> {
  Center(CConfig<P, S, AVarSum>),
  Side(P, Dir, Vec<(S, AVarSum)>),
}

impl<P: Display, S: Display> Display for RuleEnd<P, S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RuleEnd::Center(config) => write!(f, "{}", config),
      RuleEnd::Side(phase, Dir::L, right) => {
        write!(f, "phase: {}  ", phase)?;
        write!(f, "<|")?;
        if right.is_empty() {
          write!(f, " ")?;
        }
        for (s, v) in right.iter().rev() {
          write!(f, " ({}, {})", s, v)?;
        }
        Ok(())
      }
      RuleEnd::Side(phase, Dir::R, left) => {
        write!(f, "phase: {}  ", phase)?;
        for (s, v) in left.iter() {
          write!(f, "({}, {}) ", s, v)?;
        }
        if left.is_empty() {
          write!(f, " ")?;
        }
        write!(f, "|> ")?;
        Ok(())
      }
    }
  }
}

impl<P: Copy, S> RuleEnd<P, S> {
  pub fn get_phase(&self) -> P {
    match self {
      RuleEnd::Center(CConfig { state, .. }) => *state,
      RuleEnd::Side(state, ..) => *state,
    }
  }
}

// CRule for compression-rule since we're rewriting a lot of the rule stuff here
// TODO: this could be ord and hash but for now it isn't; fixable if needed
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CRule<P, S> {
  pub start: CConfig<P, S, AffineVar>,
  pub end: RuleEnd<P, S>,
}

impl<P: Display, S: Display> Display for CRule<P, S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}\ninto:\n{}", self.start, self.end)
  }
}

pub fn trans_to_rule(machine: &SmallBinMachine, edge: Edge<State, Bit>) -> CRule<State, Bit> {
  let start = CConfig {
    state: edge.0,
    left: vec![],
    head: edge.1,
    right: vec![],
  };
  let trans = machine.step(edge).unwrap();
  let (end_state, end_symbol, end_dir, trans_steps) = match trans {
    Trans::Step { state, symbol, dir, steps } => (state, symbol, dir, steps),
    _ => panic!("halt or inf trans"),
  };
  assert_eq!(trans_steps, 1);
  let end = RuleEnd::Side(end_state, end_dir, vec![(end_symbol, AVarSum::constant(1))]);

  CRule { start, end }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum VarLeftover {
  Start(AffineVar),
  End(AVarSum),
}

//invariant: the vec is never empty (so usually you have an Option<Leftover>
//and if it would have been empty it is None)
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Leftover<S> {
  Start(Vec<(S, AffineVar)>),
  End(Vec<(S, AVarSum)>),
}

pub fn match_vars(
  AVarSum { n: sum_n, var_map }: &AVarSum,
  AffineVar { n: var_n, a, var: _ }: AffineVar,
) -> Result<(), String> {
  if a != 0 || !var_map.is_empty() {
    return Err("gave up on variables".to_owned());
  }
  if *sum_n == var_n {
    Ok(())
  } else {
    Err("nums didn't match".to_owned())
  }
}

// if Err, returns string as usual
// if Ok, and the two vars did not perfectly match, returns the appropriately
// typed variable for Start or End that's leftover - so Left=Start, Right=End
// which is also enforced by start has AffineVar and end has AVarSum
pub fn match_end_vars(
  AVarSum { n: sum_n, var_map }: &AVarSum,
  AffineVar { n: var_n, a, var }: AffineVar,
) -> Result<Option<Either<AffineVar, AVarSum>>, String> {
  match (a, var_map.len()) {
    (0, 0) => match sum_n.cmp(&var_n) {
      Less => Ok(Some(Left(AffineVar::constant(var_n - sum_n)))),
      Equal => Ok(None),
      Greater => Ok(Some(Right(AVarSum::constant(sum_n - var_n)))),
    },
    (0, 1) => {
      if *sum_n >= var_n {
        //(3+x, 2) matches and leaves 1 + x
        Ok(Some(Right(AVarSum {
          n: sum_n - var_n,
          var_map: var_map.clone(),
        })))
      } else {
        //(2+x, 3) -> could match by setting x = x+1, but we aren't going that
        // route just yet
        Err("var and greater n diff sides; need a global var-tracker".to_owned())
      }
    }
    (a, 0) => {
      if var_n >= *sum_n {
        Ok(Some(Left(AffineVar { n: var_n - sum_n, a, var })))
      } else {
        Err("var and greater n diff sides; need a global var-tracker".to_owned())
      }
    }
    (a, 1) => {
      let (&avs_var, &coeff) = var_map.iter().next().unwrap();
      if var == avs_var && a == coeff {
        // matching (x+1) vs (x+2) or similar, the vars disappear and it's the
        // same as if they were never there, as above
        match sum_n.cmp(&var_n) {
          Less => Ok(Some(Left(AffineVar::constant(var_n - sum_n)))),
          Equal => Ok(None),
          Greater => Ok(Some(Right(AVarSum::constant(sum_n - var_n)))),
        }
      } else {
        Err("gave up on matching var to var at end".to_owned())
      }
    }
    (_, _) => Err("gave up on matching var to var at end".to_owned()),
  }
}

pub fn get_leftover<S: Eq + Clone>(
  end: &[(S, AVarSum)],
  start: &[(S, AffineVar)],
) -> Option<Leftover<S>> {
  match end.len().cmp(&start.len()) {
    std::cmp::Ordering::Less => {
      let diff = start.len() - end.len();
      let slice = &start[0..diff];
      Some(Leftover::Start(slice.to_owned()))
    }
    std::cmp::Ordering::Equal => None,
    std::cmp::Ordering::Greater => {
      let diff = end.len() - start.len();
      let slice = &end[0..diff];
      Some(Leftover::End(slice.to_owned()))
    }
  }
}

fn append_end_var<S>(
  mb_leftover: Option<Leftover<S>>,
  end_var_sym: S,
  end_var_match: Option<Either<AffineVar, AVarSum>>,
) -> Result<Option<Leftover<S>>, String> {
  match (mb_leftover, end_var_match) {
    (mb_leftover, None) => Ok(mb_leftover),
    (None, Some(var)) => match var {
      Left(avar) => {
        let new_leftover = vec![(end_var_sym, avar)];
        Ok(Some(Leftover::Start(new_leftover)))
      }
      Right(avarsum) => {
        let new_leftover = vec![(end_var_sym, avarsum)];
        Ok(Some(Leftover::End(new_leftover)))
      }
    },
    (Some(Leftover::Start(_)), Some(Right(_))) => Err("appended start and end".to_owned()),
    (Some(Leftover::End(_)), Some(Left(_))) => Err("appended end and start".to_owned()),
    (Some(Leftover::Start(mut lo_vec)), Some(Left(avar))) => {
      lo_vec.push((end_var_sym, avar));
      Ok(Some(Leftover::Start(lo_vec)))
    }
    (Some(Leftover::End(mut lo_vec)), Some(Right(avarsum))) => {
      lo_vec.push((end_var_sym, avarsum));
      Ok(Some(Leftover::End(lo_vec)))
    }
  }
}

// note with arbitrary tape compression the fact that we use == on S here could
// cause problems - T (FT, x) won't match (TF, x) T, and (TT, x) won't match (T, 2x)
// but we're going to stick to it for now; I think it can solve bouncers despite
// this problem, or most bouncers? and we'll see how it goes from there once
// a basic version is implemented
pub fn match_vecs<S: Eq + Clone + Debug>(
  end: &[(S, AVarSum)],
  start: &[(S, AffineVar)],
) -> Result<Option<Leftover<S>>, String> {
  match (end.len(), start.len()) {
    (0, 0) => return Ok(None),
    (_, 0) => return Ok(Some(Leftover::End(end.to_vec()))),
    (0, _) => return Ok(Some(Leftover::Start(start.to_vec()))),
    (_, _) => (),
  }
  // iter these two from back to front, but skipping the very front element
  // (of the shorter one)
  let pair_len = end.len().min(start.len());
  for offset in 1..pair_len {
    let (end_sym, end_num) = &end[end.len() - offset];
    let (start_sym, start_num) = &start[start.len() - offset];
    if end_sym != start_sym {
      return Err(format!("syms failed to match at offset {}", offset));
    }
    let _var_match = match_vars(end_num, *start_num)?;
  }
  // now handle the end of the shorter one
  let (end_sym, end_num) = &end[end.len() - pair_len];
  let (start_sym, start_num) = &start[start.len() - pair_len];
  if end_sym != start_sym {
    return Err(format!("syms failed to match at offset {}", pair_len));
  }
  let end_var_match = match_end_vars(end_num, *start_num)?;
  let leftover = get_leftover(end, start);
  let final_leftover = append_end_var(leftover, end_sym.clone(), end_var_match)?;
  Ok(final_leftover)
}

fn get_start<S: Clone>(mb_leftover: &Option<Leftover<S>>) -> Option<Vec<(S, AffineVar)>> {
  match mb_leftover {
    None => None,
    Some(Leftover::End(_)) => None,
    Some(Leftover::Start(v)) => Some(v.clone()),
  }
}

type Starts<S> = (Option<Vec<(S, AffineVar)>>, Option<Vec<(S, AffineVar)>>);

fn get_starts<S: Clone>(
  mb_leftover: &Option<Leftover<S>>,
  mb_rightover: &Option<Leftover<S>>,
) -> Starts<S> {
  (get_start(mb_leftover), get_start(mb_rightover))
}

fn get_end<S: Clone>(mb_leftover: &Option<Leftover<S>>) -> Option<Vec<(S, AVarSum)>> {
  match mb_leftover {
    None => None,
    Some(Leftover::Start(_)) => None,
    Some(Leftover::End(v)) => Some(v.clone()),
  }
}

type Ends<S> = (Option<Vec<(S, AVarSum)>>, Option<Vec<(S, AVarSum)>>);
fn get_ends<S: Clone>(
  mb_leftover: &Option<Leftover<S>>,
  mb_rightover: &Option<Leftover<S>>,
) -> Ends<S> {
  (get_end(mb_leftover), get_end(mb_rightover))
}

pub fn pop_rle_avarsum<T: Clone>(stack: &mut Vec<(T, AVarSum)>) -> Option<T> {
  let t = match stack.last_mut() {
    None => return None,
    Some((t, avarsum)) => {
      if avarsum.n == 0 {
        return None;
      } else {
        avarsum.n -= 1;
        t.clone()
      }
    }
  };
  let last_avs = &stack.last().unwrap().1;
  if last_avs.n == 0 && last_avs.var_map.is_empty() {
    stack.pop();
  };
  Some(t)
}

pub fn glue_match<P: Phase, S: Eq + Clone + Debug>(
  end: &RuleEnd<P, S>,
  CConfig {
    state: start_state,
    left: start_left,
    head: start_head,
    right: start_right,
  }: &CConfig<P, S, AffineVar>,
) -> Result<(Starts<S>, Ends<S>), String> {
  //first check intermediate states match
  if end.get_phase() != *start_state {
    return Err("phase mismatch".to_owned());
  }
  match end {
    RuleEnd::Center(CConfig {
      state: _end_state,
      left: end_left,
      head: end_head,
      right: end_right,
    }) => {
      if end_head != start_head {
        return Err("head mismatch".to_owned());
      }
      // now we need to match the left and match the right
      let left_over = match_vecs(&end_left, &start_left)?;
      let right_over = match_vecs(&end_right, &start_right)?;
      let starts = get_starts(&left_over, &right_over);
      let ends = get_ends(&left_over, &right_over);
      Ok((starts, ends))
    }
    RuleEnd::Side(_end_state, Dir::L, end_tape) => {
      let right_over = match_vecs(&end_tape, &start_right)?;
      let mut left_over_vec = start_left.clone();
      push_rle(&mut left_over_vec, start_head.clone());
      let left_over = Some(Leftover::Start(left_over_vec));
      let starts = get_starts(&left_over, &right_over);
      let ends = get_ends(&left_over, &right_over);
      Ok((starts, ends))
    }
    RuleEnd::Side(_end_state, Dir::R, end_tape) => {
      let left_over = match_vecs(&end_tape, &start_left)?;
      let mut right_over_vec = start_right.clone();
      push_rle(&mut right_over_vec, start_head.clone());
      let right_over = Some(Leftover::Start(right_over_vec));
      let starts = get_starts(&left_over, &right_over);
      let ends = get_ends(&left_over, &right_over);
      Ok((starts, ends))
    }
  }
}

pub fn append_leftover<S: Eq + Clone, T: Add<Output = T> + Clone>(
  half_tape: &[(S, T)],
  mb_leftover: Option<Vec<(S, T)>>,
) -> Vec<(S, T)> {
  match mb_leftover {
    None => half_tape.to_vec(),
    Some(mut v) => {
      append_rle(&mut v, half_tape);
      v
    }
  }
}

pub fn append_starts<P: Phase, S: Eq + Clone>(
  CConfig { state, left, head, right }: &CConfig<P, S, AffineVar>,
  starts: Starts<S>,
) -> CConfig<P, S, AffineVar> {
  CConfig {
    state: *state,
    left: append_leftover(left, starts.0),
    head: head.clone(),
    right: append_leftover(right, starts.1),
  }
}

pub fn append_ends<P: Phase, S: Eq + Clone>(
  end: &RuleEnd<P, MultiSym<S>>,
  ends: Ends<MultiSym<S>>,
) -> Result<RuleEnd<P, MultiSym<S>>, String> {
  match end {
    RuleEnd::Center(CConfig { state, left, head, right }) => Ok(RuleEnd::Center(CConfig {
      state: *state,
      left: append_leftover(left, ends.0),
      head: head.clone(),
      right: append_leftover(right, ends.1),
    })),
    RuleEnd::Side(state, Dir::L, v) => match ends.0 {
      None => Ok(RuleEnd::Side(*state, Dir::L, append_leftover(v, ends.1))),
      Some(mut lo) => {
        let head_sym = match pop_rle_avarsum(&mut lo) {
          None => return Err("couldn't sub one in appendend".to_owned()),
          Some(MultiSym::One(s)) => s,
          Some(MultiSym::Multi(mut sv)) => {
            let head_sym = sv.pop().unwrap();
            for sym in sv {
              lo.push((MultiSym::One(sym), 1.into()))
            }
            head_sym
          }
        };
        Ok(RuleEnd::Center(CConfig {
          state: *state,
          left: lo,
          head: MultiSym::One(head_sym),
          right: append_leftover(v, ends.1),
        }))
      }
    },
    RuleEnd::Side(state, Dir::R, v) => match ends.1 {
      None => Ok(RuleEnd::Side(*state, Dir::R, append_leftover(v, ends.0))),
      Some(mut lo) => {
        let head_sym = match pop_rle_avarsum(&mut lo) {
          None => return Err("couldn't sub one in appendend".to_owned()),
          Some(MultiSym::One(s)) => s,
          Some(MultiSym::Multi(mut sv)) => {
            let head_sym = sv.remove(0);
            for sym in sv.into_iter().rev() {
              lo.push((MultiSym::One(sym), 1.into()))
            }
            head_sym
          }
        };
        Ok(RuleEnd::Center(CConfig {
          state: *state,
          left: append_leftover(v, ends.0),
          head: MultiSym::One(head_sym),
          right: lo,
        }))
      }
    },
  }
}

pub fn glue_rules<P: Phase, S: Eq + Clone + Debug>(
  rule1: &CRule<P, MultiSym<S>>,
  rule2: &CRule<P, MultiSym<S>>,
) -> Result<CRule<P, MultiSym<S>>, String> {
  // first, match rule1 end to rule2 start. this obtains some ~leftovers.
  // append the start-type leftovers to rule1 start to get out's start
  // and end-type to rule2 end to get out's end
  let (starts, ends) = glue_match(&rule1.end, &rule2.start)?;
  let start = append_starts(&rule1.start, starts);
  let end = append_ends(&rule2.end, ends)?;
  Ok(CRule { start, end })
}

pub fn glue_transitions(
  machine: &SmallBinMachine,
  edges: Group<(State, Bit)>,
  print: bool,
) -> Result<CRule<State, MultiSym<Bit>>, String> {
  let mut rules = edges
    .0
    .into_iter()
    .map(|(s, b)| multi_sym_rule(&trans_to_rule(machine, Edge(s, b))));
  let mut cur_rule = match rules.next() {
    None => {
      if print {
        println!("rules was len 0 :o");
      }
      return Err("rules was len 0?".to_owned());
    }
    Some(rule) => rule,
  };
  for rule in rules {
    if print {
      println!("cur rule:\n{}", cur_rule);
      println!("gluing on:\n{}\n", rule);
    }
    match glue_rules(&cur_rule, &rule) {
      Ok(glued_rule) => {
        // if print {
        //   println!("gluing succeeded:\n{}", glued_rule);
        // }
        cur_rule = glued_rule;
      }
      Err(s) => {
        if print {
          println!("gluing failed: {}", s)
        }
        return Err(s);
      }
    }
  }
  if print {
    println!("gluing succeeded overall!\n{}", cur_rule)
  }
  Ok(cur_rule)
}

pub fn glue_rulegroup(
  machine: &SmallBinMachine,
  rulemap: &RuleMap,
  RuleGroup(Group(sv)): &RuleGroup,
  print: bool,
) -> Result<ChainRule, String> {
  if sv.len() == 0 {
    if print {
      println!("group was len 0!")
    }
    return Err("rules was len 0?".to_owned());
  }
  let mut cur_rule: ChainRule = match &sv[0] {
    Left((s, b)) => multi_sym_rule(&trans_to_rule(machine, Edge(*s, *b))),
    Right((rulename, _rulenum)) => rulemap.get(rulename).unwrap().clone(),
  };
  for (i, trans_or_rule) in sv[1..].iter().enumerate() {
    let next_rule: ChainRule = match trans_or_rule {
      Left((s, b)) => multi_sym_rule(&trans_to_rule(machine, Edge(*s, *b))),
      Right((rulename, _rulenum)) => rulemap.get(rulename).unwrap().clone(),
    };
    if print {
      println!("i:{}\ncur rule:\n{}", i, cur_rule);
      println!("gluing on:\n{}\n", next_rule);
    }
    match glue_rules(&cur_rule, &next_rule) {
      Ok(glued_rule) => {
        cur_rule = glued_rule;
      }
      Err(s) => {
        if print {
          println!("gluing failed: {}", s)
        }
        return Err(s);
      }
    }
  }
  if print {
    println!("gluing succeeded overall!\n{}", cur_rule)
  }
  Ok(cur_rule)
}

type Multi<S> = SmallVec<[S; 10]>;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum MultiSym<S> {
  One(S),
  Multi(Multi<S>),
}

impl<S: Display> Display for MultiSym<S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      MultiSym::One(s) => write!(f, "{}", s),
      MultiSym::Multi(v) => {
        f.write_char('<')?;
        for s in v {
          write!(f, "{}", s)?;
        }
        f.write_char('>')
      }
    }
  }
}

// impl<S: TapeSymbol> TapeSymbol for MultiSym<S> {
//     fn empty() -> Self {
//         todo!()
//     }

//     fn all_symbols() -> Vec<Self> {
//         todo!()
//     }
// }

pub fn multi_sym_vec<S: TapeSymbol, V: Clone>(v: &[(S, V)]) -> Vec<(MultiSym<S>, V)> {
  v.into_iter()
    .map(|(s, v)| (MultiSym::One(*s), v.clone()))
    .collect()
}

pub fn multi_sym_config<P: Phase, S: TapeSymbol, V: Clone>(
  CConfig { state, left, head, right }: &CConfig<P, S, V>,
) -> CConfig<P, MultiSym<S>, V> {
  CConfig {
    state: *state,
    left: multi_sym_vec(left),
    head: MultiSym::One(*head),
    right: multi_sym_vec(right),
  }
}

pub fn multi_sym_rule_end<P: Phase, S: TapeSymbol>(end: &RuleEnd<P, S>) -> RuleEnd<P, MultiSym<S>> {
  match end {
    RuleEnd::Center(config) => RuleEnd::Center(multi_sym_config(config)),
    RuleEnd::Side(p, d, v) => RuleEnd::Side(*p, *d, multi_sym_vec(v)),
  }
}

pub fn multi_sym_rule<P: Phase, S: TapeSymbol>(
  CRule { start, end }: &CRule<P, S>,
) -> CRule<P, MultiSym<S>> {
  CRule {
    start: multi_sym_config(start),
    end: multi_sym_rule_end(end),
  }
}

pub fn get_newest_var<P, S>(
  CRule { start: CConfig { left, right, .. }, end }: &CRule<P, S>,
) -> Var {
  let mut vars_used = HashSet::new();
  // add vars to vars_used
  add_vars_to_set(&mut vars_used, left);
  add_vars_to_set(&mut vars_used, right);
  match end {
    RuleEnd::Center(CConfig { left: left_end, right: right_end, .. }) => {
      add_vars_to_set(&mut vars_used, left_end);
      add_vars_to_set(&mut vars_used, right_end);
    }
    RuleEnd::Side(_, _, v) => {
      add_vars_to_set(&mut vars_used, v);
    }
  }

  let mut var_used_vec = vars_used.into_iter().collect_vec();
  var_used_vec.sort();
  match var_used_vec.last() {
    None => Var(0),
    Some(Var(x)) => Var(x + 1),
  }
}

pub fn flatten_multi_avar<S: Copy + Display>(
  vec: Vec<(MultiSym<S>, AffineVar)>,
) -> Result<Multi<S>, String> {
  let mut out = smallvec![];
  for (m, avar) in vec {
    match (m, avar) {
      (MultiSym::One(s), AffineVar { n, a: 0, .. }) => {
        for _ in 0..n {
          out.push(s);
        }
      }
      (m, _) => return Err(format!("m {} avar {}", m, avar)),
    }
  }
  Ok(out)
}

pub fn flatten_multi_avs<S: Copy + Display>(
  vec: Vec<(MultiSym<S>, AVarSum)>,
) -> Result<Multi<S>, String> {
  let mut out = smallvec![];
  for (m, avs) in vec {
    match (m, avs) {
      (MultiSym::One(s), AVarSum { n, var_map }) if var_map.is_empty() => {
        for _ in 0..n {
          out.push(s);
        }
      }
      (m, avs) => return Err(format!("m {} avar {}", m, avs)),
    }
  }
  Ok(out)
}

pub fn chain_var_end_leftover(
  var_chain_map: &mut VarChainMap,
  start: AffineVar,
  end: &AVarSum,
) -> Option<(AffineVar, AVarSum, Option<VarLeftover>)> {
  /*
  (x, 3) -> lower bound x to 3 (or x -> y+3) then (3+y, 3) -> (3+yk, 3)
  (x, y) -> lower bound x to y and y to x ??

   */
  match start {
    AffineVar { n, a: 0, var: _var } => {
      if end.var_map.is_empty() {
        match n.cmp(&end.n) {
          Equal => Some((start, end.clone(), None)),
          Less => {
            //(3, 4) -> (3, 3+k)
            let diff = end.n.checked_sub(n).unwrap();
            Some((
              start,
              AVarSum::from(n),
              Some(VarLeftover::End(AVarSum::from(diff))),
            ))
          }
          Greater => {
            // (5, 3) -> (3 + 2k, 3)
            let diff = n.checked_sub(end.n).unwrap();
            Some((
              end.n.into(),
              end.clone(),
              Some(VarLeftover::Start(diff.into())),
            ))
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
              let lo = if diff > 0 {
                Some(VarLeftover::End(diff.into()))
              } else {
                None
              };
              Some((start, start.into(), lo))
            } else {
              let diff = n - end.n;
              let same = AffineVar { n: end.n, a: end_a, var: end_var };
              Some((same, same.into(), Some(VarLeftover::Start(diff.into()))))
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

#[derive(Debug, Clone)]
pub struct MultiSet<S>(HashSet<Multi<S>>);

impl<S: TapeSymbol> MultiSet<S> {
  fn new() -> Self {
    MultiSet(HashSet::new())
  }

  fn cyclic_shift(repeat: &Multi<S>, shift: usize) -> Multi<S> {
    let mut out = smallvec![];
    for s in &repeat[shift..repeat.len()] {
      out.push(*s);
    }
    for s in &repeat[0..shift] {
      out.push(*s);
    }
    out
  }

  // if a cyclic shift of repeat is already present in self, returns it
  // and the starting position within repeat one must take to get it
  fn get_repeat_cyclic_shift(&self, repeat: &Multi<S>) -> Option<(Multi<S>, usize)> {
    for start_pos in 0..repeat.len() {
      let shifted = Self::cyclic_shift(repeat, start_pos);
      if self.0.contains(&shifted) {
        return Some((shifted, start_pos));
      }
    }
    None
  }

  pub fn push_multisym_rle(&self, stack: &mut Vec<(MultiSym<S>, AffineVar)>, sym: S) {
    //todo: this could push in some clever multisymbol way, but for now it doesn't
    push_rle(stack, MultiSym::One(sym));
  }

  fn get_new_repeat_avar(
    &mut self,
    mut new_repeat: Multi<S>,
    chaining_var: Var,
    dir: Dir,
  ) -> Vec<(MultiSym<S>, AffineVar)> {
    assert!(!new_repeat.is_empty());
    if dir == Dir::R {
      new_repeat.reverse();
    }
    let sym = if new_repeat.len() == 1 {
      MultiSym::One(new_repeat[0])
    } else {
      match self.get_repeat_cyclic_shift(&new_repeat) {
        None => {
          self.0.insert(new_repeat.clone());
          MultiSym::Multi(new_repeat)
        }
        Some((_, 0)) => {
          // shift amount is 0
          MultiSym::Multi(new_repeat)
        }
        //ans is [new_repeat[..shift_amount], (shifted, x-1), new_repeat[shift_amount..]]
        Some((shifted, shift_amount)) => {
          let mut out = vec![];
          for s in &new_repeat[0..shift_amount] {
            self.push_multisym_rle(&mut out, *s);
          }
          out.push((
            MultiSym::Multi(shifted),
            AffineVar { n: 0, a: 1, var: chaining_var },
          ));
          for s in &new_repeat[shift_amount..new_repeat.len()] {
            self.push_multisym_rle(&mut out, *s);
          }
          if dir == Dir::R {
            out.reverse();
          }
          return out;
        }
      }
    };
    vec![(sym, AffineVar { n: 1, a: 1, var: chaining_var })]
  }

  fn get_new_repeat_avs(
    &mut self,
    new_repeat: Multi<S>,
    chaining_var: Var,
    dir: Dir,
  ) -> Vec<(MultiSym<S>, AVarSum)> {
    let pairs = self.get_new_repeat_avar(new_repeat, chaining_var, dir);
    pairs.into_iter().map(|(s, v)| (s, v.into())).collect()
  }
}

pub fn chain_side<S: TapeSymbol>(
  start: &[(MultiSym<S>, AffineVar)],
  end: &[(MultiSym<S>, AVarSum)],
  chaining_var: Var,
  var_chain_map: &mut VarChainMap,
  multi_set: &mut MultiSet<S>,
  side_dir: Dir,
) -> Result<(Vec<(MultiSym<S>, AffineVar)>, Vec<(MultiSym<S>, AVarSum)>), String> {
  let shorter = start.len().min(end.len());
  let (mut start_out, mut end_out) = (vec![], vec![]);
  //TODO this is so gross but like, the control flow here is atrocious, idk what to do about it
  let (mut start_after_left, mut end_after_left) = (vec![], vec![]);
  // here we handle the leftovers thing
  let mb_leftover_sym = if shorter >= 1 {
    // both vecs are nonempty
    let (s_sym, s_var) = &start[start.len() - shorter];
    let (e_sym, e_var) = &end[end.len() - shorter];
    if s_sym != e_sym {
      return Err(format!("syms didn't match at position {}", 0));
    }
    let (s_var_out, e_var_out, mb_leftover) =
      match chain_var_end_leftover(var_chain_map, *s_var, e_var) {
        None => return Err(format!("vars didn't chain at position {}", 0)),
        Some(vs) => vs,
      };
    start_after_left.push((s_sym.clone(), s_var_out));
    end_after_left.push((e_sym.clone(), e_var_out));
    mb_leftover.map(|v| (s_sym, v))
  } else {
    None
  };
  match start.len().cmp(&end.len()) {
    Equal => {}
    Less => {
      let vec_tail = match mb_leftover_sym {
        None => vec![],
        Some((s, VarLeftover::End(v))) => vec![(s.clone(), v)],
        Some((_, VarLeftover::Start(_))) => return Err(format!("end longer but start leftover")),
      };
      let mut end_over = end[0..end.len() - shorter].to_vec();
      end_over.extend(vec_tail);
      let new_repeat: Multi<S> = flatten_multi_avs(end_over)?;
      // todo: encapsulate the next 4 lines of code, but also add more code
      // that causes it to like, do smart things instead of dumb things
      let end_bit = multi_set.get_new_repeat_avs(new_repeat, chaining_var, side_dir);
      end_out.extend(end_bit);
    }
    Greater => {
      let vec_tail = match mb_leftover_sym {
        None => vec![],
        Some((s, VarLeftover::Start(v))) => vec![(s.clone(), v)],
        Some((_, VarLeftover::End(_))) => return Err(format!("start longer but end leftover")),
      };
      let mut start_over = start[0..start.len() - shorter].to_vec();
      start_over.extend(vec_tail);
      let new_repeat: Multi<S> = flatten_multi_avar(start_over)?;
      let start_bit = multi_set.get_new_repeat_avar(new_repeat, chaining_var, side_dir);
      start_out.extend(start_bit);
    }
  }
  start_out.extend(start_after_left);
  end_out.extend(end_after_left);
  if shorter >= 1 {
    for (i, ((s_sym, s_var), (e_sym, e_var))) in zip_eq(
      start[start.len() - shorter + 1..].iter(),
      end[end.len() - shorter + 1..].iter(),
    )
    .enumerate()
    {
      if s_sym != e_sym {
        return Err(format!("syms didn't match at position {}", i));
      }
      let (s_var_out, e_var_out) = match chain_var(var_chain_map, *s_var, e_var, chaining_var) {
        None => return Err(format!("vars didn't chain at position {}", i)),
        Some((s_var_out, e_var_out)) => (
          s_var_out.sub_equation(chaining_var, AffineVar { n: 1, a: 1, var: chaining_var }),
          e_var_out.sub_equation(chaining_var, AffineVar { n: 1, a: 1, var: chaining_var }),
        ),
      };
      start_out.push((s_sym.clone(), s_var_out));
      end_out.push((e_sym.clone(), e_var_out));
    }
  }
  Ok((start_out, end_out))
}

pub fn chain_crule<P: Phase, S: TapeSymbol>(
  rule: &CRule<P, MultiSym<S>>,
  multi_set: &mut MultiSet<S>,
) -> Result<CRule<P, MultiSym<S>>, String> {
  /*
    so rn we get this:
  phase: D  (F, 1) |>T<|
  into:
  phase: D  (T, 1) (F, 1) |>
  we succeeded at chaining! we got:
  phase: D  (F, 1) (F, 1) |>T<| (<T>, 0 + 1*x_0)
  into:
  phase: D  (F, 1) (<T>, 1 + 1*x_0) (F, 1) |>

  which is wrong, sadly, the right answer is
  phase: D  (F, 1) |>T<| (<T>, 0 + 1*x_0)
  into:
  phase: D  (<T>, 1 + 1*x_0) (F, 1) |>

  now we get
  we succeeded at chaining! we got:
  phase: D  (F, 1) |>T<| (<T>, 0 + 1*x_0)
  into:
  phase: D  (F, 1) (<T>, 1 + 1*x_0) |>

  which is also wrong
     */
  /*
  so note that because we're a little insane, everywhere in this function, we are not
  chaining a number of times equal to chaining_var, but instead equal to chaining_var+1
  this is so we can write get_new_repeat_avar correctly.
  in the RuleEnd::Side match, we increase chaining_var by one, but that's in *addition*
  to the forgoing

  so this is pretty similar to chain_rule, and in fact we can reuse much of the
  code, but sadly we cannot reuse all of it.

  the main problem is we want to be able to chain a rule like this one:
  phase: B   |>T<| (F, 1)
  into:
  phase: B  (T, 2) |>
  the chained version of this rule looks like this:
  phase: B   |>T<| (F, 1)
  into:
  phase: B  (T, 2x+2) |>T<| (F, 1) (TF, x)
  and the thing that needs to happen here, is we *detect* that the leftover string
  on the right is TF, and then we *decide* that the string TF is a valid one to
  compress, and output this to the broader world who takes that into account in the
  future. Which, needless to say, is not something that the previous code does.

  this is implemented in two steps:
  1. check whether multi_set already contains something relevant. this will
    prevent us from eg having both TF and FT in the list, where we can instead
    only have one of them.
  2. if it does not, then we can add it to the list, and then output the rule
    with the new multi-item in it.

  */
  if rule.start.state != rule.end.get_phase() {
    return Err("phase in differed from phase out".to_owned());
  }
  let chaining_var: Var = get_newest_var(&rule);
  let mut var_chain_map = VarChainMap::new();
  let (ans, static_hm) = match &rule.end {
    RuleEnd::Center(end) => {
      if rule.start.head != end.head {
        return Err("head in differed from head out".to_owned());
      }
      let (mut left_start_out, mut left_end_out) = chain_side(
        &rule.start.left,
        &end.left,
        chaining_var,
        &mut var_chain_map,
        multi_set,
        Dir::L,
      )?;
      let (mut right_start_out, mut right_end_out) = chain_side(
        &rule.start.right,
        &end.right,
        chaining_var,
        &mut var_chain_map,
        multi_set,
        Dir::R,
      )?;
      let static_hm = var_chain_map.static_hm;
      assert!(var_chain_map.lower_bound_hm.is_empty());
      left_start_out = sub_equations_vec(left_start_out, &static_hm);
      right_start_out = sub_equations_vec(right_start_out, &static_hm);
      left_end_out = sub_equations_vec(left_end_out, &static_hm);
      right_end_out = sub_equations_vec(right_end_out, &static_hm);
      let ans = Ok(CRule {
        start: CConfig {
          state: rule.start.state,
          left: left_start_out,
          head: rule.start.head.clone(),
          right: right_start_out,
        },
        end: RuleEnd::Center(CConfig {
          state: rule.start.state,
          left: left_end_out,
          head: end.head.clone(),
          right: right_end_out,
        }),
      });

      (ans, static_hm)
    }
    RuleEnd::Side(_, Dir::L, end_right) => {
      let (mut right_start_out, mut right_end_out) = chain_side(
        &rule.start.right,
        end_right,
        chaining_var,
        &mut var_chain_map,
        multi_set,
        Dir::R,
      )?;
      /* we need this, because we're planning to chain x+1 times, to deal with the
      leftover
      once for where the head is already, and then x more times, with the lo to the L
      ie
      L >h< R
         |< R S
      becomes
      (L+h, x) L >h< R
                  |< R (S, x+1)
      */
      var_chain_map.add_static(chaining_var, AffineVar { n: 1, a: 1, var: chaining_var });

      let static_hm = var_chain_map.static_hm;
      assert!(var_chain_map.lower_bound_hm.is_empty());
      right_start_out = sub_equations_vec(right_start_out, &static_hm);
      right_end_out = sub_equations_vec(right_end_out, &static_hm);
      let mut left_over = rule.start.left.clone();
      push_rle(&mut left_over, rule.start.head.clone());
      let new_repeat: Multi<S> = flatten_multi_avar(left_over)?;
      // TODO: this is where we would do things like check for cyclic shifts of
      // new_repeat, or ensure it doesn't satisfy R = X^n, but we're not doing that
      // right now
      let mut left_start_out = multi_set.get_new_repeat_avar(new_repeat, chaining_var, Dir::L);
      left_start_out.extend(rule.start.left.clone());
      let ans = Ok(CRule {
        start: CConfig {
          state: rule.start.state,
          left: left_start_out,
          head: rule.start.head.clone(),
          right: right_start_out,
        },
        end: RuleEnd::Side(rule.start.state, Dir::L, right_end_out),
      });
      (ans, static_hm)
    }
    RuleEnd::Side(_, Dir::R, end_left) => {
      let (mut left_start_out, mut left_end_out) = chain_side(
        &rule.start.left,
        end_left,
        chaining_var,
        &mut var_chain_map,
        multi_set,
        Dir::L,
      )?;
      /* we need this, because we're planning to chain x+1 times, to deal with the
      leftover
      once for where the head is already, and then x more times, with the lo to the L
      ie
      L >h< R
         |< R S
      becomes
      (L+h, x) L >h< R
                  |< R (S, x+1)
      */
      var_chain_map.add_static(chaining_var, AffineVar { n: 1, a: 1, var: chaining_var });

      let static_hm = var_chain_map.static_hm;
      assert!(var_chain_map.lower_bound_hm.is_empty());
      left_start_out = sub_equations_vec(left_start_out, &static_hm);
      left_end_out = sub_equations_vec(left_end_out, &static_hm);
      let mut right_over = rule.start.right.clone();
      push_rle(&mut right_over, rule.start.head.clone());
      let new_repeat: Multi<S> = flatten_multi_avar(right_over)?;
      // TODO: this is where we would do things like check for cyclic shifts of
      // new_repeat, or ensure it doesn't satisfy R = X^n, but we're not doing that
      // right now
      let mut right_start_out = multi_set.get_new_repeat_avar(new_repeat, chaining_var, Dir::R);
      right_start_out.extend(rule.start.right.clone());
      let ans = Ok(CRule {
        start: CConfig {
          state: rule.start.state,
          left: left_start_out,
          head: rule.start.head.clone(),
          right: right_start_out,
        },
        end: RuleEnd::Side(rule.start.state, Dir::R, left_end_out),
      });
      (ans, static_hm)
    }
  };
  if static_hm.len() > 1 {
    println!(
      "exciting! chained\n{}\ninto\n{}\n",
      rule,
      ans.clone().unwrap()
    );
  }
  ans
}

type ChainRule = CRule<State, MultiSym<Bit>>;

type RuleName = String;

#[derive(Debug, Clone)]
pub struct RuleGroup(Group<Either<(State, Bit), (RuleName, u32)>>);

impl RuleGroup {
  fn check_same(RuleGroup(Group(sv1)): &Self, RuleGroup(Group(sv2)): &Self) -> bool {
    if sv1.len() != sv2.len() {
      return false;
    }
    for (item1, item2) in zip_eq(sv1, sv2) {
      match (item1, item2) {
        (Left(l1), Left(l2)) => {
          if l1 != l2 {
            return false;
          }
        }
        (Right((rule_name1, _rule_num1)), Right((rule_name2, _rule_num2))) => {
          if rule_name1 != rule_name2 {
            return false;
          }
        }
        (_, _) => return false,
      }
    }
    return true;
  }
}

impl Display for RuleGroup {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for mb_rule in &self.0 .0 {
      f.write_str(&display_mb_rule(mb_rule))?
    }
    Ok(())
  }
}

// a RuleGroup uses certain rules in a certain order, which is the Vec<RuleName>
// each time through the group, we use the rules at certain numbers, which is
// the second vec. the length of the Vecs inside the second vec, is the same as
// the length of the first vec. the length of the second vec, is the number of times
// this group is RLE'd.
#[derive(Debug, Clone)]
pub struct RuleNums(Vec<RuleName>, Vec<Vec<u32>>);

impl RuleNums {
  // how do we handle the case where an individual rule is used more than once?
  pub fn new(RuleGroup(Group(sv)): &RuleGroup) -> Self {
    let mut name_vec = vec![];
    let mut num_vec = vec![];
    for item in sv {
      match item {
        Left(_) => (),
        Right((rule_name, rule_num)) => {
          name_vec.push(rule_name.clone());
          num_vec.push(*rule_num);
        }
      }
    }
    Self(name_vec, vec![num_vec])
  }

  pub fn add_group(&mut self, RuleGroup(Group(sv)): &RuleGroup) {
    let mut num_vec = vec![];
    let mut name_idx = 0;
    for item in sv {
      match item {
        Left(_) => (),
        Right((rule_name, rule_num)) => {
          assert_eq!(&self.0[name_idx], rule_name);
          name_idx += 1;
          num_vec.push(*rule_num);
        }
      }
    }
    self.1.push(num_vec);
  }
}

impl Display for RuleNums {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_str("rules: ")?;
    for rule_name in &self.0 {
      write!(f, "{}, ", rule_name)?
    }
    f.write_str("\nnums:\n")?;
    for nums_vec in &self.1 {
      for num in nums_vec {
        write!(f, "{}, ", num)?
      }
      f.write_str("\n")?
    }
    Ok(())
  }
}
//output type: (group, times that group repeats, the rulenummap)
//last of which tracks what nums were used over the repeat count
pub fn rle_rule_hist(hist: &[RuleGroup]) -> Vec<(RuleGroup, u32, RuleNums)> {
  let mut out: Vec<(RuleGroup, u32, RuleNums)> = vec![];
  let mut cur_group = &hist[0];
  let mut cur_group_size = 1;
  let mut cur_rulenums = RuleNums::new(cur_group);
  for group in &hist[1..] {
    if RuleGroup::check_same(cur_group, group) {
      cur_group_size += 1;
      cur_rulenums.add_group(group);
    } else {
      out.push((cur_group.clone(), cur_group_size, cur_rulenums));
      cur_group = group;
      cur_group_size = 1;
      cur_rulenums = RuleNums::new(cur_group);
    }
  }
  out
}

type RuleMap = HashMap<String, ChainRule>;

pub fn analyze_machine(machine: &SmallBinMachine, num_steps: u32) {
  let trans_hist_with_step =
    get_transition_hist_for_machine(machine, num_steps, false).unwrap_right();
  assert_step_size_one(&trans_hist_with_step);
  let trans_hist = trans_hist_with_step
    .into_iter()
    .map(|(_steps, p, b)| (p, b))
    .collect_vec();
  println!("trans_hist:\n{}\n", display_trans_hist(&trans_hist));
  let mut rules_by_name: RuleMap = HashMap::new();
  let mut partial_rle_hist: Vec<Either<(State, Bit), (String, u32)>> =
    trans_hist.iter().map(|t| Left(*t)).collect_vec();

  let mut multi_set = MultiSet::new();
  for i in 1..=7 {
    loop {
      let grouped = group_partial_rle(&partial_rle_hist, i);
      let grouped_rle = rle_partial_rle(&grouped);
      println!("grouping by {}: {}", i, display_two_group_rle(&grouped_rle));
      let mb_new_subseq = select_next_subseq(&grouped_rle);
      if let Some(new_subseq) = mb_new_subseq {
        let subseq_str = display_trans_group(&new_subseq);
        println!("selected subseq {}", subseq_str);
        match glue_transitions(machine, new_subseq.clone(), true) {
          Err(s) => println!("gluing failed: {}", s),
          Ok(glued_rule) => {
            println!("we succeeded at gluing! we got:\n{}", glued_rule);
            match chain_crule(&glued_rule, &mut multi_set) {
              Err(s) => println!("chaining failed: {}", s),
              Ok(chained_rule) => {
                println!("we succeeded at chaining! we got:\n{}", chained_rule);
                partial_rle_hist = rle_specific_subseq(&partial_rle_hist, &new_subseq, &subseq_str);
                rules_by_name.insert(subseq_str, chained_rule);
                let partial_str = display_partial_rle_hist(&partial_rle_hist);
                println!("after grouping: {}", partial_str);
              }
            }
          }
        };
        println!();
      } else {
        println!();
        break;
      }
    }
  }
  // now we have partial_rle_hist, which is a list of Either<(State, Bit), (String, u32)>
  // we want to group-then-RLE that whole list, ignoring rights and lefts, and ignoring the u32s present in the String
  // in hopes of discovering rules that are higher than level 0 rules proven before
  // and then we want to glue+chain them, in a similar way to before, but now with
  // extra spiciness because there's lots of variables everywhere

  // to figure out which rule to generalize, we take all group sizes up to some limit
  // then we select the one which results in the largest group_num, and try abstracting
  // (via glue + chain) that one
  let mut hist = partial_rle_hist;
  let max_group_size = 100;
  let min_group_num = 5;

  let mut max_so_far_group_size = 0;
  let mut max_so_far_group_num = 1;
  let mut max_so_far_group = None;
  let mut max_so_far_rulenums = None;
  for group_size in 1..=max_group_size {
    let grouped_hist: Vec<RuleGroup> = group_any(&hist, group_size)
      .into_iter()
      .map(|x| RuleGroup(x))
      .collect();
    let rle_grouped_hist: Vec<(RuleGroup, u32, RuleNums)> = rle_rule_hist(&grouped_hist);
    // let max_group_num = rle_grouped_hist.iter().map(|(_, n, _)| *n).max().unwrap();
    let (max_group, max_group_num, max_group_rulenums) =
      rle_grouped_hist.iter().max_by_key(|(_, n, _)| n).unwrap();
    if *max_group_num > 1 {
      if max_so_far_group_num == 1 || group_size % max_so_far_group_size != 0 {
        println!(
          "grouping {} produced max_group_num {} with group {}",
          group_size, *max_group_num, max_group
        );
      }
    }

    if *max_group_num > max_so_far_group_num && *max_group_num > min_group_num {
      max_so_far_group_size = group_size;
      max_so_far_group_num = *max_group_num;
      max_so_far_group = Some(max_group.clone());
      max_so_far_rulenums = Some(max_group_rulenums.clone());
    }
  }
  if let (Some(selected_group), Some(rulenums)) = (max_so_far_group, max_so_far_rulenums) {
    println!(
      "selected a group of size {} and num {} for gluechain:\n{}\nrulenums:\n{}",
      max_so_far_group_size, max_so_far_group_num, selected_group, rulenums
    );
    println!("now gluing group");
    match glue_rulegroup(machine, &rules_by_name, &selected_group, true) {
      Err(s) => println!("gluing failed {}", s),
      Ok(glued_l1_rule) => {
        println!("we found our first l1 rule:\n{}", glued_l1_rule);
      }
    }
  } else {
    println!("didn't find any group large enough")
  }
  /*
  there's a decision point here, where there's two ways to go about the gluing

  one is to go with the sort of "bottom up" approach - we want to glue R1 to R2
  and get the maximally general result out of it.
  the advantage of this is the information flow is very simple - we have a list
  of rules and we just fold them up into one big rule.
  the disadvantage is that what is "maximally general" is not well defined and
  there are ~emergent interactions, where it isn't obvious what is "general
  enough" to work in all cases, and it might require a lot of tuning to get the
  thing to work in all cases instead of most of them.

  the other is the more "top down" approach. the only hard part of gluing, is
  gluing variables together. and we have a lot of examples of how the variables
  are set - that's what the rulenums is. the algorithm here would be to first
  look at the 2D tableau of numbers, and figure out (guess heuristically) what
  rule generates them. that's a chunk of code to write, but I think it should be
  easy-ish (famous last words). then, now that we know what the var(s) are in
  each rule, we can specify exactly what the vars are as we glue, and the gluing
  is easy, as we know always how each thing matches up - that's what the tableau
  tells us.
  the advantage of this is the gluing part is easy - there's no guesswork or
  really any room for interpretation, as we've specified what every var ought to
  be up front.
  the disadvantage is that there is extra code to write to interpret the tableau,
  and the information flow is a little more complex - the tableau is interpreted,
  then the rules get specialized, then the rules get glued. but it's not *that*
  complex, probably?
   */

  /*
  2 oct 24: we're going to start with the bottom up approach, because it is
  easier to implement, you pretty much just throw the current thing at the
  current glue code. I expect it might not work though, in which case we might
  modify the glue code but we also might try the tableau approach.

  also note that we should not create the symbol `TT` or `TTT` and fixing
  that will make the gluing work slightly better.

  okay. gluing doesn't work. there are several problems:
  1 the <TTT> thing
  2 symbols that don't match due to failures of compression, eg
    (<TF>, x), T, F not matching against (<TF>, x+1) - the former should
    not be generated
  3 the head sometimes is ><TF>< which it should not be
  4 we didn't glue (F, 1) to (F, x+1) at the end of the tape, but that
    should work I think?

  4 is fixed. we have a new problem:
  5 on machine 5, the translated bouncer with shadow, we prove a rule that is
    true, but not the one that is actually used by the machine, which we can tell
    because the rule as is is not iterable in a way that proves the machine goes
    forever. the problem is the thing where the variables are different between
    different analyzed rules:

    cur rule:
    phase: D  (T, 1) (F, 0 + 1*x_0) |>F<| (F, 1)
    into:
    phase: D  (T, 2) |>T<| (T, 0 + 1*x_0)
    gluing on:
    phase: D   |>T<| (T, 1 + 1*x_0)
    into:
    phase: D  (F, 2 + 1*x_0) |>

    gluing succeeded overall!
    phase: D  (T, 1) (F, 0 + 1*x_0) |>F<| (F, 1) (T, 1)
    into:
    phase: D  (T, 2) (F, 2 + 1*x_0) |>

    the rule "gluing on" should be applied with x_0 one smaller than
    the rule "cur rule", but the current code has no way to know this :c
    machine 8 has the same problem :c
  6 machine 2 produces:
       gluing failed: appended end and start
    due to
      cur rule:
      phase: C  (F, 2) (<TTT>, 1 + 1*x_0) (T, 2) (F, 1) |>F<|
      into:
      phase: C   |>T<| (T, 1) (<TTT>, 2 + 1*x_0) (T, 1)
      gluing on:
      phase: C  (F, 1) |>T<| (T, 1 + 1*x_0)
      into:
      phase: C  (T, 2 + 1*x_0) (F, 1) |>
    this specific case would be fixed by not creating <TTT>. is it possible to have this
    problem in general? I think maybe, but if you rule out multi-syms that are repeats
    of other multisyms, or cyclic shifts of other multisyms, then the only thing you can
    have a problem with is cases where there are at least 2 multisyms running around.

    I guess the key thing is, we need to match any 2 tapes that actually match, so in
    particular, any tape, incl. one with variables, needs to only have 1 parse. so as
    long as we enforce that, I think we're good.

    so 6 is not a new problem, it's a subproblem of 1.

    solved problem 3. remaining problems: 1, 2, 5
    1 is TTT
    2 is T, F, (<TF>, x)
    5 is vars not being synced across glues

    machines by which problem:
    0: 1
    1: 2
    2: 1
    3: 2
    4: 2
    5: 5
    6: new bug! correctness bug
    7: 2
    8: 5

    counts: 1: 2   2: 4   5: 2   plus one correctness bug :o
    4 oct: correctness bug is fixed, and 6 is now type 1, so we have
    1:3  2:4  5:2

    7 machine 6 correctness bug:
      cur rule:
      phase: C  (F, 2) (<TF>, 0 + 1*x_0) (T, 1) (F, 1) (T, 1) (<TT>, 1 + 1*x_0) (T, 2) |>T<| (F, 1)
      into:
      phase: B  (T, 1) (F, 1) |>T<| (<TF>, 1 + 1*x_0) (T, 2) (<TT>, 2 + 1*x_0)
      gluing on:
      phase: B   |>T<| (<TF>, 1 + 1*x_0)
      into:
      phase: B  (<TF>, 1 + 1*x_0) |>T<|

      cur rule:
      phase: C  (F, 2) (<TF>, 0 + 1*x_0) (T, 1) (F, 1) (T, 1) (<TT>, 1 + 1*x_0) (T, 2) |>T<| (F, 1)
      into:
      phase: B  (T, 1) (F, 1) (<TF>, 1 + 1*x_0) |>T<|
      the TT at the end is just dropped :0


   */
}

#[cfg(test)]
mod test {
  use defaultmap::defaulthashmap;
  use smallvec::ToSmallVec;

  use crate::{
    parse::{
      parse_config, parse_config_tape_side, parse_end_half_tape, parse_exact, parse_half_tape,
      parse_tape_side,
    },
    rules::Config,
  };

  use super::*;

  #[test]
  fn test_rle_encode() {
    let inp = "AAbCCC";
    let output = vec![('A', 2), ('b', 1), ('C', 3)];
    let ans = rle_encode(&inp.chars().collect_vec());
    assert_eq!(ans, output);
    let inp = "gggggggggggPPNPNppPP";
    insta::assert_debug_snapshot!(rle_encode(&inp.chars().collect_vec()), @r###"
    [
        (
            'g',
            11,
        ),
        (
            'P',
            2,
        ),
        (
            'N',
            1,
        ),
        (
            'P',
            1,
        ),
        (
            'N',
            1,
        ),
        (
            'p',
            2,
        ),
        (
            'P',
            2,
        ),
    ]
    "###);
  }

  #[test]
  fn test_group_vec() {
    let inp = group_vec(&(0..12).collect_vec(), 3);
    // panic!()
    insta::assert_debug_snapshot!(inp, @r###"
    [
        Group(
            [
                0,
                1,
                2,
            ],
        ),
        Group(
            [
                3,
                4,
                5,
            ],
        ),
        Group(
            [
                6,
                7,
                8,
            ],
        ),
        Group(
            [
                9,
                10,
                11,
            ],
        ),
    ]
    "###);
  }

  fn make_subseq(s: &str) -> (Group<char>, String) {
    (Group(s.chars().collect()), s.to_owned())
  }

  #[test]
  fn test_rle_specific_subseq() {
    let (subseq, _subseq_str) = make_subseq("aaba");
    let table = preprocess_subseq(&subseq);
    let ans = *table.get(&('a', 2)).unwrap();
    assert_eq!(ans, 2);

    let inp_str = "abcdddaddbadbddbdddddddd";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let subseq = Group(smallvec!['d']);
    let subseq_str = "d";
    let ans = rle_specific_subseq(&inp, &subseq, subseq_str);
    let ans_string = display_partial_rle_str(&ans);
    insta::assert_debug_snapshot!(ans_string, @r###""abc (d, 3) addbadbddb (d, 8) ""###);

    println!("sep ------------------------------------------------------------------------------");
    let inp_str = "bCbcADc"; // ADcAdbC";
    let subseq = Group(smallvec!['C', 'B']);
    let subseq_str = "CB";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let ans = rle_specific_subseq(&inp, &subseq, subseq_str);
    let ans_string = display_partial_rle_str(&ans);
    assert_eq!(inp_str, ans_string);

    // let inp = "bCbcADcADcAdbCBCbcADcADcADcADcAdbCBCBCbcADcADcADcADcADcADcAdbCBCBCBCbcADcADcADcADcADcADcADcADcAdbCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADc";
    let inp_str = "bCbcADcADcAdbCBCbcADcADcADcADcAdbCBCBCbcADcADcADcADcADcADcAdbCBCBCBCbcADcADcADcADcADcADcADcADcAdbCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBC";
    let subseq_1 = Group(smallvec!['C', 'B']);
    let subseq_str_1 = "CB";
    let subseq_2 = Group(smallvec!['c', 'A', 'D']);
    let subseq_str_2 = "cAD";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let intermediate = rle_specific_subseq(&inp, &subseq_1, subseq_str_1);
    let inter_string = display_partial_rle_str(&intermediate);
    let final_ans = rle_specific_subseq(&intermediate, &subseq_2, subseq_str_2);
    let final_string = display_partial_rle_str(&final_ans);
    insta::assert_debug_snapshot!(inter_string, @r###""bCbcADcADcAdbCBCbcADcADcADcADcAdbCBCBCbcADcADcADcADcADcADcAdb (CB, 3) CbcADcADcADcADcADcADcADcADcAdb (CB, 4) CbcADcADcADcADcADcADcADcADcADcADcAdb (CB, 5) CbcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 6) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 7) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 8) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 9) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 7) C""###);
    insta::assert_debug_snapshot!(final_string, @r###""bCbcADcADcAdbCBCb (cAD, 4) cAdbCBCBCb (cAD, 6) cAdb (CB, 3) Cb (cAD, 8) cAdb (CB, 4) Cb (cAD, 10) cAdb (CB, 5) Cb (cAD, 12) cAdb (CB, 6) Cb (cAD, 14) cAdb (CB, 7) Cb (cAD, 16) cAdb (CB, 8) Cb (cAD, 18) cAdb (CB, 9) Cb (cAD, 20) cAdb (CB, 7) C""###);

    // extracted from next case to shrink a failure
    let inp_str = "BaBAddDAD";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let (subseq, subseq_str) = make_subseq("DAddDA");
    let final_ans = rle_specific_subseq(&inp, &subseq, &subseq_str);
    let final_string = display_partial_rle_str(&final_ans);
    println!("final str: {}", final_string);
    assert_eq!(final_string, inp_str);

    // from fastTailEatingDragon, there's a bug where grouping doesn't happen
    // let original_inp_str = "bCbcDaBAddDADAddDADaBaBaBabCbCbCbCbcDaBAddDADAddDADaBaBaBAddDADAddDADAddDADAddDADaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBabCbCbCbCbCbCbCbCbCbCbcDaBAddDADAddDADaBaBaBAddDADAddDADAddDADAddDADaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDA";
    let inp_str = "BaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBa";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    // let grouped = group_partial_rle(&inp, 6);
    // let grouped_rle: Vec<Either<(Group<char>, u32), (Group<char>, u32)>> =
    //   rle_partial_rle(&grouped);
    // println!(
    //   "grouping by {}: {}",
    //   6,
    //   display_two_chargroup_rle(&grouped_rle)
    // );
    let (subseq, subseq_str) = make_subseq("DAddDA");
    let final_ans = rle_specific_subseq(&inp, &subseq, &subseq_str);
    let final_string = display_partial_rle_str(&final_ans);
    println!("final str: {}", final_string);
    assert_eq!(
      final_string,
      "BaBAddDA (DAddDA, 11) DaBaBaBaBaBaBaBaBaBaBaBaBa"
    );

    /* I figured out the bug. the problem is if we are looking for DAddDA
      and we see "DA DAddDA", then we start on the first DA and then when we see D,
      that's not the third letter. so we give up but don't start trying to parse the string
      again until the *next* letter, which is too late, that first D needs to be part of the
      DAddDA or it won't exist.

      it gets worse. if we just start over the parsing whenever it breaks, that isn't good enough
      either I think, maybe? we're only ever parsing one string.
      substr: aBaa
      inp_str: aB aBaa aBaa aBaa
    */
    let (subseq, subseq_str) = make_subseq("ddC");
    let inp_str = "ddddCddCddC";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let ans = rle_specific_subseq(&inp, &subseq, &subseq_str);
    let ans_string = display_partial_rle_str(&ans);
    assert_eq!(ans_string, "dd (ddC, 3) ");

    let (subseq, subseq_str) = make_subseq("aBaa");
    let inp_str = "aBaBaaaBaaaBaa";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let ans = rle_specific_subseq(&inp, &subseq, &subseq_str);
    let ans_string = display_partial_rle_str(&ans);
    assert_eq!(ans_string, "aB (aBaa, 3) ");
  }

  #[test]
  fn test_group_partial_rle() {
    // let inp_str = "bCbcADcADcAdbCBCbcADcADcADcADcAdbCBCBCbcADcADcADcADcADcADcAdbCBCBCBCbcADcADcADcADcADcADcADcADcAdbCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBC";
    // let inp = inp_str.chars().map(|c|Left(c)).collect_vec();
    // let inter = rle_encode(&group_partial_rle(&inp, 2));
    // let inter_string = display_rle_hist_gen(&inter);
    // let subseq_1 = Group(smallvec!['C', 'B']);
    // let partially_grouped = rle_specific_subseq(&inp, &subseq_1);
    // let final_ans = group_partial_rle(&partially_grouped, 3);
    // let final_string = display_partial_rle_gen(&final_ans);
    // insta::assert_debug_snapshot!(inter, @"");
    // insta::assert_yaml_snapshot!(final_string, @"");
  }

  #[test]
  fn test_chain_side() {
    // these are in the Right Side Perspective
    let start = multi_sym_vec(&parse_half_tape("(F, 1)"));
    let end = multi_sym_vec(&parse_end_half_tape("(F, 1) (T, 1)"));
    // dbg!(&start, &end);
    let res = chain_side(
      &start,
      &end,
      Var(0),
      &mut VarChainMap::new(),
      &mut MultiSet::new(),
      Dir::R,
    );
    // (F, 1) (T, x_0)
    let end_ans = vec![
      (
        MultiSym::One(Bit(true)),
        AVarSum::from(AffineVar { n: 1, a: 1, var: Var(0) }),
      ),
      (MultiSym::One(Bit(false)), 1.into()),
    ];
    assert_eq!(res, Ok((start, end_ans)));
  }

  fn config_to_cconfig<P, S, V>(
    Config { state, left, head, right }: Config<P, S, V>,
  ) -> CConfig<P, S, V> {
    CConfig { state, left, head, right }
  }

  #[test]
  fn test_match_vecs() {
    let end = vec![
      (
        Bit(true),
        AVarSum { n: 2, var_map: defaulthashmap! {0, Var(0) => 1 } },
      ),
      (Bit(false), AVarSum::constant(2)),
      (
        Bit(true),
        AVarSum { n: 1, var_map: defaulthashmap! {0, Var(0) => 1 } },
      ),
    ];
    let start = vec![(Bit(true), AffineVar { n: 1, a: 1, var: Var(0) })];
    // end is (T, x+1), (F, 2), (T, x+2)
    // start is (T, x+1)
    // so leftover should be (F, 2), (T, x+2), but on 4 oct it is None
    let ans = match_vecs(&end, &start);
    let correct = Ok(Some(Leftover::End(end[0..=1].to_owned())));
    assert_eq!(ans, correct);
  }

  #[test]
  fn test_chain_rule() {
    /*
    we succeeded at gluing! we got:
    phase: B   |>T<| (F, 1)
    into:
    phase: B  (T, 2) |>
    we succeeded at chaining! we got:
    phase: B   |>T<| (F, 1) (<FT>, 0 + 1*x_0)
    into:
    phase: B  (<TT>, 1 + 1*x_0) |>

     */
    let start_str = "phase: B   |>T<| (F, 1)";
    let start = config_to_cconfig(parse_exact(parse_config(start_str)));
    let end_tape_str = "(T, 2)";
    let end = RuleEnd::Side(State(2), Dir::R, parse_end_half_tape(end_tape_str));
    let rule = multi_sym_rule(&CRule { start, end });
    let chained_rule = chain_crule(&rule, &mut MultiSet::new()).unwrap();
    let chained_rule_str = format!("{}", chained_rule);
    let ans_str =
      "phase: B   |>T<| (F, 1) (<TF>, 1 + 1*x_0)\ninto:\nphase: B  (<TT>, 2 + 1*x_0) |> ";
    assert_eq!(chained_rule_str, ans_str);
  }
}
