use either::Either::{self, Left, Right};
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};
use std::{
  cmp::max_by_key,
  collections::{HashMap, HashSet},
  fmt::{Debug, Display, Pointer},
  hash::Hash,
  ops::{Add, AddAssign},
};

use crate::{
  brady::get_rs_hist_for_machine,
  rules::{AVarSum, AffineVar},
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

fn display_maybe_rle_char(mb_rle: &Either<char, (Group<char>, u32)>) -> String {
  match mb_rle {
    Left(c) => c.to_string(),
    Right((g, len)) => display_char_group(g, *len),
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

pub fn display_partial_rle_hist<P: Phase>(
  partial_rle_hist: &[Either<(P, Bit), (Group<(P, Bit)>, u32)>],
) -> String {
  partial_rle_hist
    .iter()
    .map(|i| display_maybe_rle(i))
    .collect()
}

pub fn display_partial_rle_str(partial_rle_hist: &[Either<char, (Group<char>, u32)>]) -> String {
  partial_rle_hist
    .iter()
    .map(|i| display_maybe_rle_char(i))
    .collect()
}

pub fn display_two_group_rle<P: Phase>(
  two_group_rle_hist: &[Either<(Group<(P, Bit)>, u32), (Group<(P, Bit)>, u32)>],
) -> String {
  two_group_rle_hist
    .iter()
    .map(|lr| match lr {
      Left((g, num)) => display_trans_rle_group(g, *num),
      Right((g, num)) => {
        let mut partial_ans = display_trans_rle_group(g, *num);
        partial_ans = partial_ans.split_off(1);
        format!(" *{}", partial_ans)
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

pub fn push_partial_rle<T: Eq>(
  stack: &mut Vec<Either<(T, u32), (T, u32)>>,
  item_or_group: Either<T, (T, u32)>,
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
pub fn rle_partial_rle<T: Eq + Clone>(
  seq: &[Either<T, (T, u32)>],
) -> Vec<Either<(T, u32), (T, u32)>> {
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

pub fn group_partial_rle<T: Debug + Copy>(
  seq: &[Either<T, (Group<T>, u32)>],
  group_size: u32,
) -> Vec<Either<Group<T>, (Group<T>, u32)>> {
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
  seq: &[Either<T, (Group<T>, u32)>],
  subseq: &Group<T>,
) -> Vec<Either<T, (Group<T>, u32)>> {
  let table: HashMap<(T, usize), usize> = preprocess_subseq(subseq);
  let min_group_count = 3;

  let mut idx_in_group: usize = 0;
  let mut group_count = 0;
  let mut out: Vec<Either<T, (Group<T>, u32)>> = vec![];

  // invariant: inp_so_far = out+(subseq, group_count)+subseq[:idx_in_group]
  for item in seq {
    match item {
      Left(t) => {
        let new_idx_in_group = *table.get(&(*t, idx_in_group)).unwrap_or(&0);
        // .unwrap_or_else(|| panic!("t {:?} idx_in_group {} subseq {:?}\nseq {:?}",
        // t, idx_in_group, subseq, seq));

        if new_idx_in_group <= idx_in_group && new_idx_in_group > 0 {
          if group_count >= min_group_count {
            out.push(Right((subseq.clone(), group_count)));
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
              out.push(Right((subseq.clone(), group_count)));
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
          out.push(Right((subseq.clone(), group_count)));
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
    out.push(Right((subseq.clone(), group_count)));
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

pub fn select_next_subseq<T: Clone>(grouped_rle: &[Either<(T, u32), (T, u32)>]) -> Option<T> {
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
  AffineVar { n: var_n, a, var: _ }: AffineVar,
) -> Result<Option<Either<AffineVar, AVarSum>>, String> {
  if a != 0 || !var_map.is_empty() {
    return Err("gave up on variables".to_owned());
  }
  match sum_n.cmp(&var_n) {
    std::cmp::Ordering::Less => Ok(Some(Left(AffineVar::constant(var_n - sum_n)))),
    std::cmp::Ordering::Equal => Ok(None),
    std::cmp::Ordering::Greater => Ok(Some(Right(AVarSum::constant(sum_n - var_n)))),
  }
}

pub fn get_leftover<S: TapeSymbol>(
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

fn append_end_var<S: TapeSymbol>(
  mb_leftover: Option<Leftover<S>>,
  end_var_sym: S,
  end_var_match: Option<Either<AffineVar, AVarSum>>,
) -> Result<Option<Leftover<S>>, String> {
  match (mb_leftover, end_var_match) {
    (_, None) => Ok(None),
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
pub fn match_vecs<S: TapeSymbol>(
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
  let final_leftover = append_end_var(leftover, *end_sym, end_var_match)?;
  Ok(final_leftover)
}

fn get_start<S: TapeSymbol>(mb_leftover: &Option<Leftover<S>>) -> Option<Vec<(S, AffineVar)>> {
  match mb_leftover {
    None => None,
    Some(Leftover::End(_)) => None,
    Some(Leftover::Start(v)) => Some(v.clone()),
  }
}

type Starts<S> = (Option<Vec<(S, AffineVar)>>, Option<Vec<(S, AffineVar)>>);

fn get_starts<S: TapeSymbol>(
  mb_leftover: &Option<Leftover<S>>,
  mb_rightover: &Option<Leftover<S>>,
) -> Starts<S> {
  (get_start(mb_leftover), get_start(mb_rightover))
}

fn get_end<S: TapeSymbol>(mb_leftover: &Option<Leftover<S>>) -> Option<Vec<(S, AVarSum)>> {
  match mb_leftover {
    None => None,
    Some(Leftover::Start(_)) => None,
    Some(Leftover::End(v)) => Some(v.clone()),
  }
}

type Ends<S> = (Option<Vec<(S, AVarSum)>>, Option<Vec<(S, AVarSum)>>);
fn get_ends<S: TapeSymbol>(
  mb_leftover: &Option<Leftover<S>>,
  mb_rightover: &Option<Leftover<S>>,
) -> Ends<S> {
  (get_end(mb_leftover), get_end(mb_rightover))
}

pub fn pop_rle_avarsum<T: Copy>(stack: &mut Vec<(T, AVarSum)>) -> Option<T> {
  let t = match stack.last_mut() {
    None => return None,
    Some((t, avarsum)) => {
      if avarsum.n == 0 {
        return None;
      } else {
        avarsum.n -= 1;
        *t
      }
    }
  };
  let last_avs = &stack.last().unwrap().1;
  if last_avs.n == 0 && last_avs.var_map.is_empty() {
    stack.pop();
  };
  Some(t)
}

pub fn glue_match<P: Phase, S: TapeSymbol>(
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
      push_rle(&mut left_over_vec, *start_head);
      let left_over = Some(Leftover::Start(left_over_vec));
      let starts = get_starts(&left_over, &right_over);
      let ends = get_ends(&left_over, &right_over);
      Ok((starts, ends))
    }
    RuleEnd::Side(_end_state, Dir::R, end_tape) => {
      let left_over = match_vecs(&end_tape, &start_left)?;
      let mut right_over_vec = start_right.clone();
      push_rle(&mut right_over_vec, *start_head);
      let right_over = Some(Leftover::Start(right_over_vec));
      let starts = get_starts(&left_over, &right_over);
      let ends = get_ends(&left_over, &right_over);
      Ok((starts, ends))
    }
  }
}

pub fn append_leftover<S: TapeSymbol, T: Add<Output = T> + Clone>(
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

pub fn append_starts<P: Phase, S: TapeSymbol>(
  CConfig { state, left, head, right }: &CConfig<P, S, AffineVar>,
  starts: Starts<S>,
) -> CConfig<P, S, AffineVar> {
  CConfig {
    state: *state,
    left: append_leftover(left, starts.0),
    head: *head,
    right: append_leftover(right, starts.1),
  }
}

pub fn append_ends<P: Phase, S: TapeSymbol>(
  end: &RuleEnd<P, S>,
  ends: Ends<S>,
) -> Result<RuleEnd<P, S>, String> {
  match end {
    RuleEnd::Center(CConfig { state, left, head, right }) => Ok(RuleEnd::Center(CConfig {
      state: *state,
      left: append_leftover(left, ends.0),
      head: *head,
      right: append_leftover(right, ends.1),
    })),
    RuleEnd::Side(state, Dir::L, v) => match ends.0 {
      None => Ok(RuleEnd::Side(*state, Dir::L, append_leftover(v, ends.1))),
      Some(mut lo) => {
        let s = match pop_rle_avarsum(&mut lo) {
          None => return Err("couldn't sub one in appendend".to_owned()),
          Some(s) => s,
        };
        Ok(RuleEnd::Center(CConfig {
          state: *state,
          left: lo,
          head: s,
          right: append_leftover(v, ends.1),
        }))
      }
    },
    RuleEnd::Side(state, Dir::R, v) => match ends.1 {
      None => Ok(RuleEnd::Side(*state, Dir::R, append_leftover(v, ends.0))),
      Some(mut lo) => {
        let s = match pop_rle_avarsum(&mut lo) {
          None => return Err("couldn't sub one in appendend".to_owned()),
          Some(s) => s,
        };
        Ok(RuleEnd::Center(CConfig {
          state: *state,
          left: append_leftover(v, ends.0),
          head: s,
          right: lo,
        }))
      }
    },
  }
}

pub fn glue_rules<P: Phase, S: TapeSymbol>(
  rule1: &CRule<P, S>,
  rule2: &CRule<P, S>,
) -> Result<CRule<P, S>, String> {
  // first, match rule1 end to rule2 start. this obtains some ~leftovers.
  // append the start-type leftovers to rule1 start to get out's start
  // and end-type to rule2 end to get out's end
  let (starts, ends) = glue_match(&rule1.end, &rule2.start)?;
  // dbg!(&starts, &ends);
  let start = append_starts(&rule1.start, starts);
  let end = append_ends(&rule2.end, ends)?;
  Ok(CRule { start, end })
}

pub fn glue_transitions(
  machine: &SmallBinMachine,
  edges: Group<(State, Bit)>,
  print: bool,
) -> Result<CRule<State, Bit>, String> {
  let mut rules = edges
    .0
    .into_iter()
    .map(|(s, b)| trans_to_rule(machine, Edge(s, b)));
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

pub fn analyze_machine(machine: &SmallBinMachine, num_steps: u32) {
  let trans_hist_with_step =
    get_transition_hist_for_machine(machine, num_steps, false).unwrap_right();
  assert_step_size_one(&trans_hist_with_step);
  let trans_hist = trans_hist_with_step
    .into_iter()
    .map(|(_steps, p, b)| (p, b))
    .collect_vec();
  println!("trans_hist:\n{}\n", display_trans_hist(&trans_hist));
  let mut partial_rle_hist = trans_hist.iter().map(|t| Left(*t)).collect_vec();

  for i in 1..=7 {
    loop {
      let grouped = group_partial_rle(&partial_rle_hist, i);
      let grouped_rle = rle_partial_rle(&grouped);
      println!("grouping by {}: {}", i, display_two_group_rle(&grouped_rle));
      let mb_new_subseq = select_next_subseq(&grouped_rle);
      if let Some(new_subseq) = mb_new_subseq {
        println!("selected subseq {}", display_trans_group(&new_subseq));
        partial_rle_hist = rle_specific_subseq(&partial_rle_hist, &new_subseq);
        let partial_str = display_partial_rle_hist(&partial_rle_hist);
        println!("after grouping: {}", partial_str);
        match glue_transitions(machine, new_subseq, true) {
          Err(s) => println!("gluing failed: {}", s),
          Ok(glued_rule) => {
            //todo: display for CRule
            println!("we succeeded at gluing! we got:\n{}", glued_rule);
          }
        };

        println!();
      } else {
        println!();
        break;
      }
    }
  }
}

#[cfg(test)]
mod test {
  use smallvec::ToSmallVec;

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

  fn make_subseq(s: &str) -> Group<char> {
    Group(s.chars().collect())
  }

  #[test]
  fn test_rle_specific_subseq() {
    let subseq = make_subseq("aaba");
    let table = preprocess_subseq(&subseq);
    let ans = *table.get(&('a', 2)).unwrap();
    assert_eq!(ans, 2);

    let inp_str = "abcdddaddbadbddbdddddddd";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let subseq = Group(smallvec!['d']);
    let ans = rle_specific_subseq(&inp, &subseq);
    let ans_string = display_partial_rle_str(&ans);
    insta::assert_debug_snapshot!(ans_string, @r###""abc (d, 3) addbadbddb (d, 8) ""###);

    println!("sep ------------------------------------------------------------------------------");
    let inp_str = "bCbcADc"; // ADcAdbC";
    let subseq = Group(smallvec!['C', 'B']);
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let ans = rle_specific_subseq(&inp, &subseq);
    let ans_string = display_partial_rle_str(&ans);
    assert_eq!(inp_str, ans_string);

    // let inp = "bCbcADcADcAdbCBCbcADcADcADcADcAdbCBCBCbcADcADcADcADcADcADcAdbCBCBCBCbcADcADcADcADcADcADcADcADcAdbCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADc";
    let inp_str = "bCbcADcADcAdbCBCbcADcADcADcADcAdbCBCBCbcADcADcADcADcADcADcAdbCBCBCBCbcADcADcADcADcADcADcADcADcAdbCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBCBCBCbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdbCBCBCBCBCBCBCBC";
    let subseq_1 = Group(smallvec!['C', 'B']);
    let subseq_2 = Group(smallvec!['c', 'A', 'D']);
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let intermediate = rle_specific_subseq(&inp, &subseq_1);
    let inter_string = display_partial_rle_str(&intermediate);
    let final_ans = rle_specific_subseq(&intermediate, &subseq_2);
    let final_string = display_partial_rle_str(&final_ans);
    insta::assert_debug_snapshot!(inter_string, @r###""bCbcADcADcAdbCBCbcADcADcADcADcAdbCBCBCbcADcADcADcADcADcADcAdb (CB, 3) CbcADcADcADcADcADcADcADcADcAdb (CB, 4) CbcADcADcADcADcADcADcADcADcADcADcAdb (CB, 5) CbcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 6) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 7) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 8) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 9) CbcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcADcAdb (CB, 7) C""###);
    insta::assert_debug_snapshot!(final_string, @r###""bCbcADcADcAdbCBCb (cAD, 4) cAdbCBCBCb (cAD, 6) cAdb (CB, 3) Cb (cAD, 8) cAdb (CB, 4) Cb (cAD, 10) cAdb (CB, 5) Cb (cAD, 12) cAdb (CB, 6) Cb (cAD, 14) cAdb (CB, 7) Cb (cAD, 16) cAdb (CB, 8) Cb (cAD, 18) cAdb (CB, 9) Cb (cAD, 20) cAdb (CB, 7) C""###);

    // extracted from next case to shrink a failure
    let inp_str = "BaBAddDAD";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let subseq = make_subseq("DAddDA");
    let final_ans = rle_specific_subseq(&inp, &subseq);
    let final_string = display_partial_rle_str(&final_ans);
    println!("final str: {}", final_string);
    assert_eq!(final_string, inp_str);

    // from fastTailEatingDragon, there's a bug where grouping doesn't happen
    // let original_inp_str = "bCbcDaBAddDADAddDADaBaBaBabCbCbCbCbcDaBAddDADAddDADaBaBaBAddDADAddDADAddDADAddDADaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBabCbCbCbCbCbCbCbCbCbCbcDaBAddDADAddDADaBaBaBAddDADAddDADAddDADAddDADaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBaBAddDADAddDADAddDADAddDADAddDA";
    let inp_str = "BaBAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADAddDADaBaBaBaBaBaBaBaBaBaBaBaBa";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let grouped = group_partial_rle(&inp, 6);
    let grouped_rle: Vec<Either<(Group<char>, u32), (Group<char>, u32)>> =
      rle_partial_rle(&grouped);
    println!(
      "grouping by {}: {}",
      6,
      display_two_chargroup_rle(&grouped_rle)
    );
    let subseq = make_subseq("DAddDA");
    println!("\n\n\nstart wrong one ---------------------------------------------------\n");
    let final_ans = rle_specific_subseq(&inp, &subseq);
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
    let subseq = make_subseq("ddC");
    let inp_str = "ddddCddCddC";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let ans = rle_specific_subseq(&inp, &subseq);
    let ans_string = display_partial_rle_str(&ans);
    assert_eq!(ans_string, "dd (ddC, 3) ");

    let subseq = make_subseq("aBaa");
    let inp_str = "aBaBaaaBaaaBaa";
    let inp = inp_str.chars().map(|c| Left(c)).collect_vec();
    let ans = rle_specific_subseq(&inp, &subseq);
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
}
