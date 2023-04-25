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
  simulate::{ExpTape, Signature, TapeChange, TapeChangeKind, TapeHalf},
  turing::{
    Bit,
    Dir::{self, L, R},
    Edge, State, TapeSymbol, Trans, Turing, HALT, INFINITE, START,
  },
};
use defaultmap::{defaulthashmap, DefaultHashMap};
use either::Either::{self, Left, Right};
use itertools::{chain, zip_eq, Itertools};
use proptest::{prelude::*, sample::select};
use smallvec::{smallvec, SmallVec};
use std::{
  cmp::Ordering::*,
  collections::{HashMap, HashSet},
  iter::zip,
  ops::Add,
};
use std::{collections::hash_map::Iter, hash::Hash};
use std::{
  fmt::{Debug, Display, Write},
  ops::AddAssign,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Var(pub u8);

impl Display for Var {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "x_{}", self.0)
  }
}

//ax + n
#[derive(Debug, Hash, Clone, Copy)]
pub struct AffineVar {
  pub n: u32,
  pub a: u32,
  pub var: Var,
}

impl PartialEq for AffineVar {
  fn eq(&self, other: &Self) -> bool {
    self.n == other.n && self.a == other.a && (self.var == other.var || self.a == 0)
  }
}

impl Eq for AffineVar {}

impl From<u32> for AffineVar {
  fn from(value: u32) -> Self {
    AffineVar::constant(value)
  }
}

impl From<SymbolVar> for AffineVar {
  fn from(SymbolVar { n, a, var }: SymbolVar) -> Self {
    AffineVar { n: n.try_into().unwrap(), a, var }
  }
}

impl Add for AffineVar {
  type Output = Self;
  fn add(self, rhs: Self) -> Self::Output {
    if self.a > 0 && rhs.a > 0 && self.var != rhs.var {
      panic!("tried to add incompatible avars: {} {}", self, rhs);
    }
    AffineVar {
      n: self.n + rhs.n,
      a: self.a + rhs.a,
      var: self.var,
    }
  }
}

impl AddAssign for AffineVar {
  fn add_assign(&mut self, rhs: Self) {
    if self.a > 0 && rhs.a > 0 && self.var != rhs.var {
      panic!("tried to add incompatible avars: {} {}", self, rhs);
    }
    self.n += rhs.n;
    self.a += rhs.a;
  }
}

impl AffineVar {
  pub fn constant(n: u32) -> Self {
    Self { n, a: 0, var: Var(0) }
  }

  pub fn sub<C: TapeCount>(&self, x: C) -> C {
    let &AffineVar { n, a, var: _var } = self;
    // return n + a * x;
    return C::add(n.into(), x.mul_const(a));
  }

  pub fn sub_map_maybe<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> Option<C> {
    if self.a == 0 {
      Some(self.sub(C::zero()))
    } else {
      let &x = hm.get(&self.var)?;
      Some(self.sub(x))
    }
  }

  pub fn sub_map<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> C {
    self.sub_map_maybe(hm).unwrap()
  }

  pub fn times_var(self, var: Var) -> Option<Self> {
    if self.a == 0 {
      Some(Self { n: 0, a: self.n, var })
    } else {
      println!("var times var {}", self);
      None
    }
  }
}

impl Display for AffineVar {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.a == 0 {
      write!(f, "{}", self.n)
    } else {
      write!(f, "{} + {}*{}", self.n, self.a, self.var)
    }
  }
}

trait Subbable {
  // fn sub<C: TapeCount>(&self, x: C) -> C;
  // fn sub_map_maybe<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> Option<C>;
  // fn sub_map<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> C {
  //   self.sub_map_maybe(hm).unwrap()
  // }
  fn update_var(self, neg_map: &DefaultHashMap<Var, i32>) -> Self;
}

impl Subbable for AffineVar {
  // fn sub_map_maybe<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> Option<C> {
  //   self.sub_map_maybe(hm)
  // }
  fn update_var(self, neg_map: &DefaultHashMap<Var, i32>) -> Self {
    update_affine_var(self, neg_map)
  }
}

// much like Tape / ExpTape, the *last* thing in the Vec is the closest to the head,
// for both left and right
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Config<S, V> {
  pub state: State,
  pub left: Vec<(S, V)>,
  pub head: S,
  pub right: Vec<(S, V)>,
}

impl<S: Display + Copy, V: Display> Display for Config<S, V> {
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

impl<S> Config<S, AffineVar> {
  fn vec_u32_to_avar(u32s: Vec<(S, u32)>) -> Vec<(S, AffineVar)> {
    u32s
      .into_iter()
      .map(|(s, u32)| (s, AffineVar::constant(u32)))
      .collect()
  }

  fn from_tape_state(state: State, ExpTape { left, head, right }: ExpTape<S, u32>) -> Self {
    Self {
      state,
      left: Config::vec_u32_to_avar(left),
      head,
      right: Config::vec_u32_to_avar(right),
    }
  }

  fn to_tape_state(self) -> (State, ExpTape<S, SymbolVar>) {
    match self {
      Config { state, left, head, right } => {
        let tape = ExpTape { left, head, right };
        (state, tape.map_first(|avar| avar.into()))
      }
    }
  }
}

pub fn av_to_avs<S>(avs: Vec<(S, AffineVar)>) -> Vec<(S, AVarSum)> {
  avs
    .into_iter()
    .map(|(s, avar)| (s, AVarSum::from(avar)))
    .collect()
}

impl<S> Config<S, AVarSum> {
  pub fn from_avars(
    Config { state, left, head, right }: Config<S, AffineVar>,
  ) -> Config<S, AVarSum> {
    Self::new_from_avars(state, left, head, right)
  }

  pub fn new_from_avars(
    state: State,
    left: Vec<(S, AffineVar)>,
    head: S,
    right: Vec<(S, AffineVar)>,
  ) -> Self {
    Self {
      state,
      left: av_to_avs(left),
      head,
      right: av_to_avs(right),
    }
  }

  fn to_tape_state(self) -> Option<(State, ExpTape<S, SymbolVar>)> {
    match self {
      Config { state, left, head, right } => {
        let tape = ExpTape { left, head, right };
        let new_tape: ExpTape<S, SymbolVar> = tape
          .map_first_maybe(|avar| TryInto::<AffineVar>::try_into(avar).ok().map(|x| x.into()))?;
        Some((state, new_tape))
      }
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Rule<S> {
  pub start: Config<S, AffineVar>,
  pub end: Config<S, AVarSum>,
}

impl<S: Display + Copy> Display for Rule<S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}\ninto:\n{}", self.start, self.end)
  }
}

impl<S: TapeSymbol> Rule<S> {
  pub fn start_edge_index(&self) -> usize {
    match self {
      Rule {
        start: Config { state, left: _left, head, right: _right },
        end: _end,
      } => return Edge(*state, *head).edge_index(),
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

  pub fn add_rules(&mut self, rules: Vec<Rule<S>>) {
    for rule in rules {
      self.add_rule(rule);
    }
  }
  pub fn get_rules(&self, edge: Edge<S>) -> &Vec<Rule<S>> {
    &self.1[edge.edge_index()]
  }

  pub fn chain_rulebook(machine: &impl Turing<S>) -> Self {
    let chain_rules = detect_chain_rules(machine);
    let mut rulebook = Rulebook::new(machine.num_states());
    rulebook.add_rules(chain_rules);
    rulebook
  }
}

pub trait TapeCount: Copy + Eq + Hash + Debug + Display + From<u32> {
  fn zero() -> Self;
  fn add(x: Self, y: Self) -> Self;
  fn mul_const(self, n: u32) -> Self;
  fn match_var(
    avar: AffineVar,
    count: Self,
    verbose: bool,
  ) -> Option<(Either<u32, Self>, Option<(Var, Self)>)>;
  fn sub_one(self) -> Self;
}

// illegal, very sad
// impl<C: TapeCount> AddAssign for C {
//   fn add_assign(&mut self, rhs: Self) {
//     *self = Self::add(self, rhs)
//   }
// }

pub fn match_var_num(
  AffineVar { n, a, var }: AffineVar,
  mut num: u32,
  verbose: bool,
) -> Option<(Either<u32, u32>, Option<(Var, u32)>)> {
  // returns
  // 0: the num left to match in the avar or the num left on the tape
  // 1: what to send the var to.
  if num < n {
    if verbose {
      println!("num")
    };
    if a == 0 {
      return Some((Left(n.checked_sub(num).unwrap()), None));
    } else {
      return None;
    }
  }
  num -= n;
  if a == 0 {
    return Some((Right(num), None));
  }
  if num < a {
    return None;
  } // sending var to 1 would be too big
  Some((Right(num % a), Some((var, num / a))))
}

impl TapeCount for u32 {
  fn zero() -> Self {
    0
  }

  fn add(x: Self, y: Self) -> Self {
    x + y
  }

  fn mul_const(self, n: u32) -> Self {
    self * n
  }

  fn match_var(
    avar: AffineVar,
    count: Self,
    verbose: bool,
  ) -> Option<(Either<u32, Self>, Option<(Var, Self)>)> {
    match_var_num(avar, count, verbose)
  }

  fn sub_one(self) -> Self {
    self - 1
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuleTapeMatch<S, C> {
  ConsumedEnd((S, AffineVar)),
  Leftover(C),
}
use RuleTapeMatch::*;

impl<S: TapeSymbol, C> RuleTapeMatch<S, C> {
  fn empty_ify(opt_rtm: Option<RuleTapeMatch<S, C>>) -> Option<RuleTapeMatch<S, C>> {
    if let Some(ConsumedEnd((s, _avar))) = opt_rtm {
      if s != S::empty() {
        return None;
      }
    }
    return opt_rtm;
  }
}

pub fn match_rule_tape<S: TapeSymbol, C: TapeCount>(
  hm: &mut HashMap<Var, C>,
  rule: &[(S, AffineVar)],
  tape: &[(S, C)],
  verbose: bool,
) -> Option<RuleTapeMatch<S, C>> {
  // if rule applies, returns
  // 0: how much of the last elt is leftover
  // 1: how many elements
  // else returns none
  let mut leftover = Right(C::zero());
  if rule.len() > tape.len() + 1 {
    if verbose {
      println!("rule too long")
    };
    return None;
  };

  let mut last_elt_empty_tape = false;
  let mut tape_change_val_sym = None;
  if rule.len() == tape.len() + 1 {
    let last_rule_pair = rule.first().unwrap();
    // if last_rule_pair.0 == S::empty() {
    //we can match the empty characters implicitly represented by the end of the tape
    if verbose {
      println!(
        "matched {}, {} to empty",
        last_rule_pair.0, last_rule_pair.1
      )
    };
    last_elt_empty_tape = true;
    tape_change_val_sym = Some(last_rule_pair);
  }
  let rule_slice_start = if last_elt_empty_tape { 1 } else { 0 };
  for (&(rule_symbol, avar), &(tape_symbol, num)) in
    zip(rule[rule_slice_start..].iter().rev(), tape.iter().rev())
  {
    if leftover != Right(C::zero()) {
      if verbose {
        println!("some bits leftover {}", leftover)
      };
      return None;
    }
    if verbose {
      println!(
        "matching {}, {} to {}, {}",
        rule_symbol, avar, tape_symbol, num
      )
    };
    if rule_symbol != tape_symbol {
      if verbose {
        println!("symbols didn't match")
      };
      return None;
    }
    let (new_leftover, mb_new_var) = C::match_var(avar, num, verbose)?;

    leftover = new_leftover;
    if let Some((var, var_num)) = mb_new_var {
      match hm.get(&var) {
        None => {
          hm.insert(var, var_num);
        }
        Some(&old_var_num) => {
          if var_num != old_var_num {
            if verbose {
              println!("var {} sent to both: {} {}", var, old_var_num, var_num)
            };
            return None;
          }
        }
      }
    }
  }
  match tape_change_val_sym {
    Some(tape_change_val_sym) => {
      if leftover != Right(C::zero()) {
        return None;
      } else {
        return Some(ConsumedEnd(*tape_change_val_sym));
      }
    }
    None => match leftover {
      Left(eat_past_end) => {
        return Some(ConsumedEnd((rule.get(0).unwrap().0, eat_past_end.into())))
      }
      Right(leftover) => return Some(Leftover(leftover)),
    },
  }
}

pub fn remove<T>(vec: &mut Vec<T>, to_remove: usize) {
  vec.truncate(vec.len() - to_remove)
}

pub fn consume_tape_from_rulematch<S: TapeSymbol, C: TapeCount>(
  tape: &mut Vec<(S, C)>,
  tape_match: RuleTapeMatch<S, C>,
  rule_len: usize,
) {
  match tape_match {
    ConsumedEnd(_avar) => remove(tape, rule_len - 1),
    Leftover(leftover) if leftover == TapeCount::zero() => remove(tape, rule_len),
    Leftover(leftover) => {
      remove(tape, rule_len - 1);
      tape.last_mut().unwrap().1 = leftover;
    }
  }
}

pub fn append_rule_tape<S: TapeSymbol, C: TapeCount>(
  hm: &HashMap<Var, C>,
  rule: &[(S, AVarSum)],
  tape: &mut Vec<(S, C)>,
) -> Option<AVarSum> {
  // the avar is the amount we shrank the tape by, if any
  let (slice_to_append, shrink_amount) = match rule.get(0) {
    None => return None,
    Some((s, avar)) => match tape.last_mut() {
      None => {
        if *s == S::empty() {
          (&rule[1..], Some(avar.clone()))
        } else {
          (&rule[..], None)
        }
      }
      Some((t, num)) => {
        if s == t {
          *num = C::add(*num, avar.sub_map(hm));
          (&rule[1..], None)
        } else {
          (&rule[..], None)
        }
      }
    },
  };
  tape.extend(
    slice_to_append
      .iter()
      .map(|(s, avar)| (*s, avar.sub_map(hm))),
  );
  shrink_amount
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RuleTapeChangeSide {
  grew: Option<AffineVar>,
  shrunk: Option<AVarSum>,
}

impl RuleTapeChangeSide {
  pub fn empty() -> Self {
    Self { grew: None, shrunk: None }
  }

  pub fn from_tapechangekind(tck: TapeChangeKind) -> Self {
    match tck {
      TapeChangeKind::Grew => Self { grew: Some(AffineVar::constant(1)), shrunk: None },
      TapeChangeKind::Shrunk => Self { grew: None, shrunk: Some(AVarSum::constant(1)) },
    }
  }

  pub fn from_ruletapematch_and_shrink_amount<S: TapeSymbol, C>(
    rtm: RuleTapeMatch<S, C>,
    shrink_amount: Option<AVarSum>,
  ) -> Self {
    let grow_amount = match rtm {
      ConsumedEnd((_, avar)) => Some(avar),
      Leftover(_) => None,
    };
    Self { grew: grow_amount, shrunk: shrink_amount }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RuleTapeChange {
  left: RuleTapeChangeSide,
  right: RuleTapeChangeSide,
}

impl RuleTapeChange {
  pub fn from_tapechange(tc: TapeChange) -> Self {
    match tc {
      None => Self {
        left: RuleTapeChangeSide::empty(),
        right: RuleTapeChangeSide::empty(),
      },
      Some((Dir::L, tck)) => Self {
        left: RuleTapeChangeSide::from_tapechangekind(tck),
        right: RuleTapeChangeSide::empty(),
      },
      Some((Dir::R, tck)) => Self {
        left: RuleTapeChangeSide::empty(),
        right: RuleTapeChangeSide::from_tapechangekind(tck),
      },
    }
  }
}

pub fn apply_rule_extra_info<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  cur_state: State,
  Rule { start: Config { state, left, head, right }, end }: &Rule<S>,
  verbose: bool,
) -> Option<Either<Var, (State, HashMap<Var, C>, RuleTapeChange)>> {
  /*
  Option<_>: rule might not apply. if it does, returns
  Left: a Var which was sent to infinity
  Right: (no var was sent to infinity) the new state, the identities of all the vars, and
      the amount the tape grew or shrunk
   */
  if verbose {
    println!(
      "trying out rule {}\nto\n{}",
      Config {
        state: *state,
        left: left.clone(),
        head: *head,
        right: right.clone()
      },
      end
    );
  }
  if cur_state == *state && tape.head == *head {
    let mut hm = HashMap::new();
    if verbose {
      println!("left")
    };
    let left_match = RuleTapeMatch::empty_ify(match_rule_tape(&mut hm, left, &tape.left, verbose))?;
    if verbose {
      println!("right")
    };
    let right_match =
      RuleTapeMatch::empty_ify(match_rule_tape(&mut hm, right, &tape.right, verbose))?;
    if verbose {
      println!("succeeded")
    };
    if let ConsumedEnd((_, avar)) = left_match {
      if let None = avar.sub_map_maybe(&hm) {
        return Some(Left(avar.var));
      }
    }
    if let ConsumedEnd((_, avar)) = right_match {
      if let None = avar.sub_map_maybe(&hm) {
        return Some(Left(avar.var));
      }
    }
    consume_tape_from_rulematch(&mut tape.left, left_match, left.len());
    consume_tape_from_rulematch(&mut tape.right, right_match, right.len());
    let shrink_left = append_rule_tape(&hm, &end.left, &mut tape.left);
    let shrink_right = append_rule_tape(&hm, &end.right, &mut tape.right);
    tape.head = end.head;
    let rule_tape_change = RuleTapeChange {
      left: RuleTapeChangeSide::from_ruletapematch_and_shrink_amount(left_match, shrink_left),
      right: RuleTapeChangeSide::from_ruletapematch_and_shrink_amount(right_match, shrink_right),
    };
    return Some(Right((end.state, hm, rule_tape_change)));
  } else {
    return None;
  }
}

pub fn apply_rule<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  cur_state: State,
  rule: &Rule<S>,
  verbose: bool,
) -> Option<Either<Var, State>> {
  match apply_rule_extra_info(tape, cur_state, rule, verbose) {
    None => None,
    Some(Left(v)) => Some(Left(v)),
    Some(Right((s, _hm, _rtc))) => Some(Right(s)),
  }
}

pub fn apply_rules<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  state: State,
  rulebook: &Rulebook<S>,
  verbose: bool,
) -> Option<Either<Var, (State, HashMap<Var, C>, RuleTapeChange)>> {
  let edge = Edge(state, tape.head);
  let rules = rulebook.get_rules(edge);
  for rule in rules {
    match apply_rule_extra_info(tape, state, rule, verbose) {
      None => (),
      Some(ans) => return Some(ans),
    }
  }
  return None;
}

pub fn one_rule_step<S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<S>,
  exptape: &mut ExpTape<S, C>,
  state: State,
  rulebook: &Rulebook<S>,
  step: u32,
  verbose: bool,
) -> Either<Var, (State, HashMap<Var, C>, RuleTapeChange)> {
  let (new_state, hm, rtc) = match apply_rules(exptape, state, rulebook, verbose) {
    Some(Left(var)) => return Left(var),
    Some(Right(res)) => {
      println!("rule_applied");
      res
    }
    None => match exptape.step_extra_info(state, machine) {
      Left(_edge) => unreachable!("machine is defined"),
      Right((state, tc)) => (
        state,
        HashMap::default(),
        RuleTapeChange::from_tapechange(tc),
      ),
    },
  };
  if verbose {
    println!("step: {} phase: {} tape: {}", step, new_state, exptape);
  }
  return Right((new_state, hm, rtc));
}

pub fn simulate_using_rules<S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<S>,
  num_steps: u32,
  rulebook: &Rulebook<S>,
  verbose: bool,
) -> (State, u32, ExpTape<S, C>) {
  let mut exptape = ExpTape::new();
  let mut state = START;
  for step in 1..num_steps + 1 {
    state = match one_rule_step(machine, &mut exptape, state, rulebook, step, verbose) {
      Left(_var) => return (INFINITE, step, exptape),
      Right((s, _, _)) => s,
    };
    if state == HALT {
      return (HALT, step, exptape);
    }
    println!("step: {} phase: {} tape: {}", step, state, exptape);
  }
  return (state, num_steps, exptape);
}

fn collate<S: TapeSymbol>(
  (f_sym, f_num): (S, u32),
  (s_sym, s_num): (S, u32),
) -> ((S, AffineVar), (S, AffineVar), bool) {
  // bool is was there a var used
  assert_eq!(f_sym, s_sym);
  match f_num.cmp(&s_num) {
    Less => (
      (f_sym, AffineVar { n: 0, a: 1, var: Var(0) }),
      (
        s_sym,
        AffineVar {
          n: s_num.checked_sub(f_num).expect("we used cmp"),
          a: 1,
          var: Var(0),
        },
      ),
      true,
    ),
    Equal => (
      (f_sym, AffineVar::constant(f_num)),
      (s_sym, AffineVar::constant(s_num)),
      false,
    ),
    Greater => (
      (
        f_sym,
        AffineVar {
          n: f_num.checked_sub(s_num).expect("we used cmp"),
          a: 1,
          var: Var(0),
        },
      ),
      (s_sym, AffineVar { n: 0, a: 1, var: Var(0) }),
      true,
    ),
  }
}

fn make_side<S: TapeSymbol>(
  start: &[(S, u32)],
  end: &[(S, u32)],
  final_size: i32,
  max_size: i32,
) -> (Vec<(S, AffineVar)>, Vec<(S, AffineVar)>, bool) {
  assert_eq!(start.len(), end.len());
  let start_grow_amount = max_size;
  let end_grow_amount = max_size - final_size;
  let mut start_out = if start_grow_amount != 0 {
    vec![(
      S::empty(),
      AffineVar::constant(start_grow_amount.try_into().unwrap()),
    )]
  } else {
    vec![]
  };
  let mut end_out = if end_grow_amount != 0 {
    vec![(
      S::empty(),
      AffineVar::constant(end_grow_amount.try_into().unwrap()),
    )]
  } else {
    vec![]
  };

  let mut var_used = false;
  for (&s, &e) in zip(start, end) {
    let (s_var, e_var, was_var) = collate(s, e);
    var_used = var_used || was_var;
    start_out.push(s_var);
    end_out.push(e_var);
  }
  (start_out, end_out, var_used)
}

/*
 we need to figure out how to deal with the fact that the tape shrinks and grows
 if the tape has overall shrunk, then we need to expand the end of the rule
 if the tape has overall grown, we need to expand the start of the rule
 but that's not sufficient, if a tape grows by 1 then shrinks by 1, we need to grow both the
 start and the end by 1
 so essentially we need to track the maximum size that side of the tape has ever been
 then grow both the start and the end to there
 so that looks like
 tape_changes : [int]
 tape_sizes = [0]
 for tc in tape_changes:
   tape_sizes.append(tape_sizes[-1] + tc)
 maximum_size_of_tape = max(tape_sizes)

 amount_to_grow_start = maximum_size_of_tape
 amount_to_grow_end = maximum_size_of_tape - tape_sizes[-1]
*/
pub fn accumulate_tape_diffs(tape_diffs: &[SmallVec<[TapeDiff; 4]>]) -> (i32, i32, i32, i32) {
  let mut left_size = 0;
  let mut max_left_size = 0;

  let mut right_size = 0;
  let mut max_right_size = 0;

  for sv_tape_diff in tape_diffs {
    for tape_diff in sv_tape_diff {
      match tape_diff {
        TapeDiff(Dir::L, diff) => {
          left_size += diff;
          max_left_size = max_left_size.max(left_size);
        }
        TapeDiff(Dir::R, diff) => {
          right_size += diff;
          max_right_size = max_right_size.max(right_size);
        }
      }
    }
  }
  (left_size, max_left_size, right_size, max_right_size)
}

pub fn detect_rule<S: TapeSymbol>(
  history: &Vec<(u32, State, ExpTape<S, u32>)>,
  (final_left_size, max_left_size, final_right_size, max_right_size): (i32, i32, i32, i32),
) -> Vec<Rule<S>> {
  /* we're detecting an additive rule, so any numbers that don't change, we guess don't change
  and any numbers that do change, we guess change by that constant each time
  so we need to
  1) make vectors of the change amount
  2) zip those vectors with the signatures and turn them into configs
  */
  let second_last = &history[history.len() - 2];
  let last = &history[history.len() - 1];
  let (start_left, end_left, var_used_left) = make_side(
    &second_last.2.left,
    &last.2.left,
    final_left_size,
    max_left_size,
  );
  let (start_right, end_right, var_used_right) = make_side(
    &second_last.2.right,
    &last.2.right,
    final_right_size,
    max_right_size,
  );
  if !var_used_left && !var_used_right {
    return vec![];
  }
  let rule = Rule {
    start: Config {
      state: second_last.1,
      left: start_left,
      head: second_last.2.head,
      right: start_right,
    },
    end: Config::new_from_avars(last.1, end_left, last.2.head, end_right),
  };
  vec![rule]
}

pub fn detect_rules<S: TapeSymbol>(
  step: u32,
  state: State,
  exptape: &ExpTape<S, u32>,
  signatures: &mut DefaultHashMap<Signature<S>, Vec<(u32, State, ExpTape<S, u32>)>>,
  tape_diffs: &Vec<SmallVec<[TapeDiff; 4]>>,
) -> Vec<Rule<S>> {
  let cur_sig_vec = &mut signatures[exptape.signature()];
  cur_sig_vec.push((step, state, exptape.clone()));
  if cur_sig_vec.len() > 1 {
    let steps = cur_sig_vec.iter().map(|(s, _, _)| s).collect_vec();
    let second_last_step = *steps[steps.len() - 2] as usize;
    let last_step = *steps[steps.len() - 1] as usize;
    let tape_diff_range = &tape_diffs[second_last_step..last_step];
    let tape_sizes = accumulate_tape_diffs(tape_diff_range);
    let rules = detect_rule(cur_sig_vec, tape_sizes);
    if rules.len() > 0 {
      println!(
        "using steps: {:?} detected rule:\n{}\n",
        steps,
        rules.first().unwrap()
      );
    }
    return rules;
  }
  return vec![];
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TapeDiffError {
  GrewArb,
  ShrunkArb,
}
use TapeDiffError::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TapeDiff(Dir, i32);

fn rtcs_to_ints(
  out: &mut SmallVec<[TapeDiff; 4]>,
  hm: &HashMap<Var, u32>,
  d: Dir,
  RuleTapeChangeSide { grew, shrunk }: RuleTapeChangeSide,
) -> Result<(), TapeDiffError> {
  if let Some(grew) = grew {
    match grew.sub_map_maybe(hm) {
      None => {
        return Err(TapeDiffError::GrewArb);
      }
      Some(c) => out.push(TapeDiff(d, c.try_into().unwrap())),
    }
  }
  if let Some(shrunk) = shrunk {
    match shrunk.sub_map_maybe(hm) {
      None => return Err(TapeDiffError::ShrunkArb),
      Some(c) => out.push(TapeDiff(d, i32::try_from(c).unwrap() * -1)),
    }
  }
  Ok(())
}

fn rtc_to_tape_diffs(
  hm: &HashMap<Var, u32>,
  RuleTapeChange { left, right }: RuleTapeChange,
) -> Result<SmallVec<[TapeDiff; 4]>, TapeDiffError> {
  // unfortuantely you can both grow and shrink the tape
  // and you have to process that sequentially, not all at once
  let mut out = smallvec![];
  let left_res = rtcs_to_ints(&mut out, hm, Dir::L, left);
  let right_res = rtcs_to_ints(&mut out, hm, Dir::R, right);
  match (left_res, right_res) {
    (Err(GrewArb), _) => return Err(GrewArb),
    (_, Err(GrewArb)) => return Err(GrewArb),
    (Err(ShrunkArb), _) => panic!("shrunkarb without grewarb"),
    (_, Err(ShrunkArb)) => panic!("shrunkarb without grewarb"),
    (Ok(()), Ok(())) => (),
  }
  Ok(out)
}

// pub fn simulate_detect_rules<S: TapeSymbol>(
//   machine: &impl Turing<S>,
//   num_steps: u32,
//   rulebook: &Rulebook<S>,
//   verbose: bool,
// ) -> (State, u32) {
//   /*
//   the plan to detect rules:
//   store the signatures of everything seen so far
//   if you see the same signature more than once, there is a possible rule
//   */
//   let mut exptape = ExpTape::new();
//   let mut state = START;
//   // let mut rulebook = Rulebook::new(machine.num_states());
//   let mut signatures: DefaultHashMap<Signature<S>, Vec<(u32, State, ExpTape<S, u32>)>> =
//     defaulthashmap!();
//   let mut tape_diffs = vec![];
//   for step in 1..num_steps + 1 {
//     let (new_state, hm, rtc) = one_rule_step(machine, &mut exptape, state, rulebook, step, verbose);
//     state = new_state;
//     match rtc_to_tape_diffs(&hm, rtc) {
//       Err(GrewArb) => return (INFINITE, step),
//       Err(ShrunkArb) => unreachable!("never returned"),
//       Ok(tape_diff) => tape_diffs.push(tape_diff),
//     }

//     if state == HALT {
//       return (HALT, step);
//     }
//     detect_rules(step, state, &exptape, &mut signatures, &tape_diffs);
//   }

//   return (state, num_steps);
// }

pub fn detect_chain_rules<S: TapeSymbol>(machine: &impl Turing<S>) -> Vec<Rule<S>> {
  /* whenever there is a transition XS -> XTD for state X, symbols S,T, dir D
    there is a chain rule (X, >S< S^n) -> (X, T^n >T<) (shown here for R).
  */
  let mut out = vec![];
  for state_in in machine.all_states() {
    for symbol_in in S::all_symbols() {
      let Trans { state: state_out, symbol: symbol_out, dir } = machine
        .step(Edge(state_in, symbol_in))
        .expect("machine is defined");
      if state_in == state_out {
        let sym_var = AffineVar { n: 0, a: 1, var: Var(0) };
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
            let end = Config::new_from_avars(state_in, vec![], symbol_in, half_tape_out);
            out.push(Rule { start, end });
          }
          R => {
            let start = Config {
              state: state_in,
              left: vec![],
              head: symbol_in,
              right: half_tape_in,
            };
            let end = Config::new_from_avars(state_in, half_tape_out, symbol_in, vec![]);
            out.push(Rule { start, end });
          }
        }
      }
    }
  }
  out
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum RuleProof {
  DirectSimulation(u32),
}
use RuleProof::*;

// a var that we use on the tape and are trying to generalize
// it can be subtracted from, in case that is helpful
#[derive(Debug, Hash, Clone, Copy)]
pub struct SymbolVar {
  pub n: i32,
  pub a: u32,
  pub var: Var,
}

impl PartialEq for SymbolVar {
  fn eq(&self, other: &Self) -> bool {
    self.n == other.n && self.a == other.a && (self.var == other.var || self.a == 0)
  }
}

impl Eq for SymbolVar {}

impl Display for SymbolVar {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.a == 0 {
      write!(f, "{}", self.n)
    } else {
      write!(f, "{} + {}*a_{}", self.n, self.a, self.var.0)
    }
  }
}

impl From<u32> for SymbolVar {
  fn from(value: u32) -> Self {
    SymbolVar::constant(value.try_into().unwrap())
  }
}

impl TryFrom<AVarSum> for SymbolVar {
  type Error = ();
  fn try_from(avarsum: AVarSum) -> Result<Self, Self::Error> {
    let avar = AffineVar::try_from(avarsum)?;
    Ok(avar.into())
  }
}

impl TryFrom<AVarSum> for AffineVar {
  type Error = ();

  fn try_from(value: AVarSum) -> Result<Self, Self::Error> {
    if value.var_map.is_empty() {
      return Ok(AffineVar { n: value.n, a: 0, var: Var(0) });
    }

    match value.var_map.iter().exactly_one() {
      Err(_) => return Err(()),
      Ok((&v, &a)) => return Ok(AffineVar { n: value.n, a, var: v }),
    }
  }
}

impl SymbolVar {
  pub fn constant(n: i32) -> Self {
    Self { n, a: 0, var: Var(0) }
  }
}

impl TapeCount for SymbolVar {
  fn zero() -> Self {
    SymbolVar::constant(0)
  }

  fn add(SymbolVar { n, a, var }: Self, SymbolVar { n: m, a: b, var: var2 }: Self) -> Self {
    //todo oh no this is a mess
    if var != var2 {
      panic!("added incompatible symbolvars")
    }
    SymbolVar { n: n + m, a: a + b, var }
  }

  fn mul_const(self, multiplier: u32) -> Self {
    let SymbolVar { n, a, var } = self;
    SymbolVar {
      n: n * i32::try_from(multiplier).unwrap(),
      a: a * multiplier,
      var: var,
    }
  }
  fn match_var(
    avar: AffineVar,
    count: Self,
    _verbose: bool,
  ) -> Option<(Either<u32, Self>, Option<(Var, Self)>)> {
    match_avar_svar(avar, count)
  }

  fn sub_one(self) -> Self {
    let Self { n, a, var } = self;
    Self { n: n - 1, a, var }
  }
}

impl From<AffineVar> for SymbolVar {
  fn from(AffineVar { n, a, var }: AffineVar) -> Self {
    SymbolVar { n: n as i32, a, var }
  }
}

pub fn match_avar_svar(
  AffineVar { n, a, var: avar }: AffineVar,
  mut svar: SymbolVar,
) -> Option<(Either<u32, SymbolVar>, Option<(Var, SymbolVar)>)> {
  // returns
  // 0: either the unmatched avar or the svar left on the tape
  // 1: what to send the var in the affinevar to
  /*
  examples (avar match svar)
  5 match 6 returns 1
  5 match 4 returns None
  5 match a returns a - 5

  x match _ returns (0, (x -> _))

  2x match 6 returns (0, (x -> 3))
  2x match 7 returns (1, (x -> 3))
  2x match a returns None
  2x match 3a returns (a, (x -> a))
  2x match 2a - 1 returns (1, (x -> a-1))

  2x+3 match 6 returns (1, (x -> 1))
  2x+3 match 7 returns (0, (x -> 2))
  2x+3 match a returns None
  2x+3 match 2a returns (1, (x -> a-2))
  2x+3 match 3a returns (a-3, (x -> a))


  general rule: the integer always applies
  the var leaves the smallest non-negative integer possible,
  and the smallest non-negative coefficient of the symbolvar
   */
  svar.n -= i32::try_from(n).unwrap();
  if svar.n < 0 && svar.a == 0 {
    return Some((Left(svar.n.abs().try_into().unwrap()), None));
  }

  if a == 0 {
    return Some((Right(svar), None));
  }

  if svar.a > 0 && a > svar.a {
    return None;
  }
  let coeff_a_in_x = svar.a / a;
  svar.a = svar.a % a;
  let a_i32 = i32::try_from(a).unwrap();
  let integer_in_x = svar.n.div_euclid(a_i32);
  svar.n = svar.n.rem_euclid(a_i32);
  Some((
    Right(svar),
    Some((
      avar,
      SymbolVar { n: integer_in_x, a: coeff_a_in_x, var: svar.var },
    )),
  ))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AVarSum {
  pub n: u32,
  pub var_map: DefaultHashMap<Var, u32>,
}

impl Display for AVarSum {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.n)?;
    for (v, a) in self.var_map.iter() {
      write!(f, " + {}*{}", a, v)?;
    }
    Ok(())
  }
}

impl From<AffineVar> for AVarSum {
  fn from(avar: AffineVar) -> Self {
    let mut out = Self::new();
    out.add_avar(avar);
    out
  }
}

impl Add for AVarSum {
  type Output = AVarSum;
  fn add(mut self, rhs: Self) -> Self::Output {
    self.add_avs(rhs);
    self
  }
}

impl AddAssign for AVarSum {
  fn add_assign(&mut self, rhs: Self) {
    self.add_avs(rhs);
  }
}

impl AVarSum {
  fn new() -> Self {
    AVarSum { n: 0, var_map: defaulthashmap! {0} }
  }

  fn constant(n: u32) -> Self {
    AVarSum { n, var_map: defaulthashmap! {0} }
  }

  fn sub_map_maybe<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> Option<C> {
    let mut out: C = self.n.into();
    for (v, a) in self.var_map.iter() {
      let &c = hm.get(v)?;
      out = C::add(out, c.mul_const(*a));
    }
    Some(out)
  }

  fn sub_map<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> C {
    self
      .sub_map_maybe(hm)
      .expect(&format!("subbing {} using {:?}", self, hm))
  }

  fn add_avs(&mut self, AVarSum { n, var_map }: AVarSum) {
    self.n += n;
    for (v, a) in var_map.iter() {
      self.var_map[*v] += a;
    }
  }

  fn add_avar(&mut self, AffineVar { n, a, var }: AffineVar) {
    self.n += n;
    if a > 0 {
      self.var_map[var] += a;
    }
  }

  fn mb_sub_avar(&mut self, AffineVar { n, a, var }: AffineVar) -> Option<()> {
    if a > self.var_map[var] || n > self.n {
      return None;
    }
    self.n -= n;
    self.var_map[var] -= a;
    Some(())
  }

  fn modify_tapechange(
    &mut self,
    RuleTapeChangeSide { grew, shrunk }: RuleTapeChangeSide,
  ) -> Option<()> {
    if let Some(grew) = grew {
      self.mb_sub_avar(grew)?;
    }
    if let Some(shrunk) = shrunk {
      self.add_avs(shrunk);
    }
    Some(())
  }

  fn times_var(&self, var: Var) -> Option<AffineVar> {
    if self.var_map.len() > 0 {
      return None;
    }
    return Some(AffineVar { n: 0, a: self.n, var });
  }
}

impl Subbable for AVarSum {
  fn update_var(mut self, neg_map: &DefaultHashMap<Var, i32>) -> Self {
    for (v, a) in self.var_map.iter() {
      let amt_changed: u32 = neg_map[v].abs().try_into().unwrap();
      self.n += a * amt_changed;
    }
    self
  }
}

fn process_tape_side<S: TapeSymbol>(side: &mut Vec<(S, SymbolVar)>) -> AVarSum {
  match side.get(0).map(|x| x.clone()) {
    Some((sym, sv)) if sym == S::empty() => {
      side.remove(0);
      let mut sum = AVarSum::new();
      if sv.a > 0 {
        panic!("can't handle nonzero sv")
      }
      sum.n += u32::try_from(sv.n).unwrap();
      sum
    }
    Some((_sym, _sv)) => AVarSum::new(),
    None => AVarSum::new(),
  }
}

fn process_goal_tape<S: TapeSymbol>(
  ExpTape { mut left, head, mut right }: ExpTape<S, SymbolVar>,
) -> (ExpTape<S, SymbolVar>, AVarSum, AVarSum) {
  /* if you're trying to prove a goal tape like
   |>F<| (T, 1 + 1*x_0) (F, 1)
  you will have the problem the (F, 1) gets dropped into the void
  so this processes that into the tape with no empty symbols at the end
  and also what the dropped variables should be
  */
  let left_sum = process_tape_side(&mut left);
  let right_sum = process_tape_side(&mut right);
  (ExpTape { left, right, head }, left_sum, right_sum)
}

pub fn prove_rule<S: TapeSymbol>(
  machine: &impl Turing<S>,
  rule: Rule<S>,
  rulebook: &Rulebook<S>,
  prover_steps: u32,
  too_negative: i32,
  verbose: bool,
) -> Option<(Rule<S>, RuleProof)> {
  if verbose {
    println!("working to prove rule: {}", &rule);
  }

  let Rule { start, end } = rule;
  let (mut state, mut proving_tape) = start.clone().to_tape_state();
  let (goal_state, goal_tape) = match end.clone().to_tape_state() {
    Some(ans) => ans,
    None => {
      if verbose {
        println!("failed to prove rule, because end did not convert to svars")
      }
      return None;
    }
  };
  let (goal_tape, left_goal_sum, right_goal_sum) = process_goal_tape(goal_tape);

  let mut neg_map: DefaultHashMap<Var, i32> = defaulthashmap! {0};
  let mut left_shrink = AVarSum::new();
  let mut right_shrink = AVarSum::new();

  for step in 1..prover_steps + 1 {
    let (new_state, hm, tc) =
      one_rule_step(machine, &mut proving_tape, state, rulebook, step, verbose).right()?;
    // if we ever try to grow the tape more than we have already shrunk it, then we
    // immediately fail
    let ls_res = left_shrink.modify_tapechange(tc.left);
    let rs_res = right_shrink.modify_tapechange(tc.right);
    if ls_res.is_none() || rs_res.is_none() {
      if verbose {
        println!("proving the rule failed because we hit the end of the tape")
      }
      return None;
    }
    if verbose {
      // println!("ls: {:?} rs: {:?}", left_shrink, right_shrink);
    }

    state = new_state;
    /*
    we need to track over time how negative each symbolvar has become, so that we can later
    modify the rule to prevent the symbolvar from becoming negative. symbolvars exist
    both in the hm and in the proving_tape.

    we also give up if a symbolvar becomes too_negative, because probably that means we
    can't prove this rule
     */
    for &SymbolVar { n, a: _a, var } in chain!(
      hm.iter().map(|(_, sv)| sv),
      proving_tape.left.iter().map(|(_, sv)| sv),
      proving_tape.right.iter().map(|(_, sv)| sv),
    ) {
      neg_map[var] = neg_map[var].min(n);
      if neg_map[var] < too_negative {
        if verbose {
          println!("proving the rule failed due to negativity");
        }
        return None;
      }
    }

    // check if we succeeded
    if state == goal_state
      && proving_tape == goal_tape
      && left_shrink == left_goal_sum
      && right_shrink == right_goal_sum
    {
      if verbose {
        println!("proving the rule suceeded");
      }
      return Some((
        package_rule(Rule { start, end }, &neg_map),
        DirectSimulation(step),
      ));
    }
  }
  if verbose {
    println!("proving the rule failed");
  }
  return None;
}

fn update_affine_var(
  AffineVar { n, a, var }: AffineVar,
  neg_map: &DefaultHashMap<Var, i32>,
) -> AffineVar {
  let amt_changed: u32 = neg_map[var].abs().try_into().unwrap();
  let amt_to_add = a * amt_changed;
  AffineVar { n: n + amt_to_add, a, var }
}

fn update_config<S, V: Subbable>(
  Config { state, left, head, right }: Config<S, V>,
  neg_map: &DefaultHashMap<Var, i32>,
) -> Config<S, V> {
  Config {
    state,
    left: left
      .into_iter()
      .map(|(s, avar)| (s, V::update_var(avar, neg_map)))
      .collect(),
    head: head,
    right: right
      .into_iter()
      .map(|(s, avar)| (s, V::update_var(avar, neg_map)))
      .collect(),
  }
}

fn package_rule<S: TapeSymbol>(
  Rule { start, end }: Rule<S>,
  neg_map: &DefaultHashMap<Var, i32>,
) -> Rule<S> {
  Rule {
    start: update_config(start, neg_map),
    end: update_config(end, neg_map),
  }
}

pub fn simulate_proving_rules<S: TapeSymbol>(
  machine: &impl Turing<S>,
  num_steps: u32,
  rulebook: &mut Rulebook<S>,
  verbose: bool,
) -> (State, u32) {
  /*
  the plan to detect rules:
  store the signatures of everything seen so far
  if you see the same signature more than once, there is a possible rule
  */
  let mut exptape = ExpTape::new();
  let mut state = START;
  let mut signatures: DefaultHashMap<Signature<S>, Vec<(u32, State, ExpTape<S, u32>)>> =
    defaulthashmap!();
  let mut tape_diffs = vec![];
  for step in 1..num_steps + 1 {
    if verbose {
      println!("starting step {}", step);
    }
    let (new_state, hm, rtc) =
      match one_rule_step(machine, &mut exptape, state, rulebook, step, verbose) {
        Left(_var) => {
          if verbose {
            println!("proved machine runs forever using a rule");
          }
          return (INFINITE, step);
        }
        Right(ans) => ans,
      };
    state = new_state;
    match rtc_to_tape_diffs(&hm, rtc) {
      Err(GrewArb) => return (INFINITE, step),
      Err(ShrunkArb) => unreachable!("never returned"),
      Ok(tape_diff) => tape_diffs.push(tape_diff),
    }
    if verbose {
      // println!("tape diffs: {:?}", tape_diffs.last())
    }

    if state == HALT {
      return (HALT, step);
    }

    let rules = detect_rules(step, state, &exptape, &mut signatures, &tape_diffs);
    for rule in rules {
      if let Some((final_rule, pf)) = prove_rule(machine, rule, rulebook, 20, -5, verbose) {
        println!("proved rule: \n{}\nvia proof{:?}", final_rule, pf);
        if let Some(chained_rule) = chain_rule(&final_rule) {
          println!("chained the proved rule to: {}", chained_rule);
          rulebook.add_rule(chained_rule);
        }
        rulebook.add_rule(final_rule);
      }
    }
  }
  return (state, num_steps);
}

pub fn chain_var(
  hm: &HashMap<Var, SymbolVar>,
  start: AffineVar,
  end: &AVarSum,
  chaining_var: Var,
) -> Option<(AffineVar, AVarSum)> {
  /*
  (3, 3) => (3, 3)
  (3, x) => (3, 3)
  (x, x+2) => (x, x+2y)
  // todo:
  // decreases are trickier
  (x+1, x) => (x, 0) + x = y
  (x+3, x) => [(3x, 0), (3x+1, 1), (3x+2, 2)]
  maybe you write the above as x -> x mod 3 or something?

  // also, note that (x, 0) is going as far as possible, which is usually what you want, but not
  always, in particular, if you are proving a rule
   */
  match start {
    AffineVar { n, a: 0, var: _var } => {
      if end.var_map.is_empty() {
        let ans = n.min(end.n);
        Some((AffineVar::constant(ans), AVarSum::constant(ans)))
      } else {
        assert_eq!(SymbolVar::from(start), end.sub_map(hm));
        Some((start, start.into()))
      }
    }
    AffineVar { n, a, var } => {
      if end.var_map.is_empty() {
        let sub_start = start.sub_map(hm);
        assert_eq!(&AVarSum::from(AffineVar::from(sub_start)), end);
        return Some((sub_start.into(), AVarSum::from(AffineVar::from(sub_start))));
      }
      match end.var_map.iter().exactly_one() {
        Err(_) => {
          // warning
          println!("tried to chain {} into {} and couldn't #1", start, end);
          return None;
        }
        Ok((&var2, &b)) => {
          if var != var2 || a != b || n > end.n {
            println!("tried to chain {} into {} and couldn't #2", start, end);
            return None;
          }
          // (ax + n, ax + m) -> (ax + n, ax + n + k*(m - n))
          let mut end_out: AVarSum = start.into();
          let coeff_chain_var = end.n.checked_sub(n).unwrap();
          if coeff_chain_var > 0 {
            end_out.add_avar(AffineVar { n: 0, a: coeff_chain_var, var: chaining_var });
          }
          Some((start, end_out))
        }
      }
    }
  }
}

trait GetVars {
  fn get_vars(&self) -> impl Iterator<Item = Var> + '_;
}

impl GetVars for AffineVar {
  fn get_vars(&self) -> impl Iterator<Item = Var> {
    if self.a == 0 {
      vec![].into_iter()
    } else {
      vec![self.var].into_iter()
    }
  }
}

impl GetVars for AVarSum {
  fn get_vars(&self) -> impl Iterator<Item = Var> + '_ {
    self.var_map.iter().map(|(v, _)| *v)
  }
}

fn add_vars_to_set<S, V: GetVars>(hs: &mut HashSet<Var>, stuff: &Vec<(S, V)>) {
  for (_, av) in stuff.iter() {
    for v in V::get_vars(av) {
      hs.insert(v);
    }
  }
}

pub fn get_newest_var<S>(
  Rule {
    start: Config { state: _state, left, head: _head, right },
    end:
      Config {
        state: __state,
        left: end_left,
        head: __head,
        right: end_right,
      },
  }: &Rule<S>,
) -> Var {
  let mut vars_used = HashSet::new();
  add_vars_to_set(&mut vars_used, left);
  add_vars_to_set(&mut vars_used, right);
  add_vars_to_set(&mut vars_used, end_left);
  add_vars_to_set(&mut vars_used, end_right);
  let mut var_used_vec = vars_used.into_iter().collect_vec();
  var_used_vec.sort();
  match var_used_vec.get(0) {
    None => Var(0),
    Some(Var(x)) => Var(x + 1),
  }
}

pub fn append_exptape<S: Eq, C: AddAssign>(tape: &mut Vec<(S, C)>, item: (S, C)) {
  match tape.last_mut() {
    None => tape.push(item),
    Some((tape_s, tape_c)) => {
      if *tape_s == item.0 {
        *tape_c += item.1;
      } else {
        tape.push(item);
      }
    }
  }
}

pub fn chain_side<S: TapeSymbol>(
  start: &Vec<(S, AffineVar)>,
  end: &Vec<(S, AVarSum)>,
  new_var: Var,
) -> Option<(Vec<(S, AffineVar)>, Vec<(S, AVarSum)>)> {
  if start.len().abs_diff(end.len()) > 1 {
    return None;
  }
  #[derive(Debug, Clone, Copy)]
  enum StartEnd {
    Start,
    End,
  }
  use StartEnd::*;

  let mut hm = HashMap::new();
  let end_sv = end
    .iter()
    .map(|(s, avar)| {
      SymbolVar::try_from(avar.clone())
        .ok()
        .map(|svar| (*s, svar))
    })
    .collect::<Option<Vec<(S, SymbolVar)>>>()?;

  let rtm = match_rule_tape(&mut hm, start, &end_sv, false)?;

  //two usize are where to iterate from in start and end resp.
  let (ans, start_slice, end_slice): ((StartEnd, S, AffineVar), usize, usize) = match rtm {
    // in this case, we add (s, avar)*n to the start
    ConsumedEnd((s, avar)) => {
      let ans = (Start, s, avar.times_var(new_var)?);
      let start_slice = if end.len() + 1 == start.len() {
        1
      } else if end.len() == start.len() {
        0
      } else {
        assert_eq!(end.len(), start.len() + 1);
        return None;
      };
      (ans, start_slice, 0)
    }
    // in this case, we add (?, svar)*n to the end, but also have to fuck around to
    // make sure about the end of the tape
    /* three cases:
    if tape is shorter than rule, we have to be in the above
    if tape is equal to rule, we can have zero leftover, or positive leftover and multiply it
    if tape is longer than rule, we can only have zero leftover, or we fail
    */
    Leftover(svar) => {
      if end.len() == start.len() + 1 {
        if svar == SymbolVar::constant(0) {
          let (end_s, end_v) = end.get(0).unwrap();
          ((End, *end_s, end_v.times_var(new_var)?), 0, 1)
        } else {
          return None;
        }
      } else {
        assert_eq!(end.len(), start.len());
        //todo: this svar can be negative
        if svar == SymbolVar::constant(0) {
          ((End, S::empty(), AffineVar::constant(0)), 0, 0)
        } else {
          (
            (
              End,
              end.get(0).unwrap().0,
              AffineVar::from(svar).times_var(new_var)?,
            ),
            0,
            0,
          )
        }
      }
    }
  };
  let (mut start_out, mut end_out) = match ans {
    (_, _s, AffineVar { n: 0, a: 0, var: _var }) => (vec![], vec![]),
    (Start, s, v) => (vec![(s, v)], vec![]),
    (End, s, v) => (vec![], vec![(s, v.into())]),
  };

  for (i, (&(s_sym, s_var), (e_sym, e_var))) in
    zip_eq(start[start_slice..].iter(), end[end_slice..].iter()).enumerate()
  {
    let (s_var_out, e_var_out) = chain_var(&mut hm, s_var, e_var, new_var)?;
    if i == 0 {
      append_exptape(&mut start_out, (s_sym, s_var_out));
      append_exptape(&mut end_out, (*e_sym, e_var_out));
    } else {
      start_out.push((s_sym, s_var_out));
      end_out.push((*e_sym, e_var_out));
    }
  }
  Some((start_out, end_out))
}

pub fn chain_rule<S: TapeSymbol>(
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
  }: &Rule<S>,
) -> Option<Rule<S>> {
  // we're going to match the start to the end
  // and then have to deal with all the ends in a nasty way
  if state_start != state_end {
    return None;
  }
  if head_start != head_end {
    return None;
  }
  let chaining_var: Var = get_newest_var(&rule);
  let (left_start_out, left_end_out) = chain_side(left_start, left_end, chaining_var)?;
  let (right_start_out, right_end_out) = chain_side(right_start, right_end, chaining_var)?;
  Some(Rule {
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
  })
}

pub mod parse {

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
    simulate::ExpTape,
    turing::{Bit, State, AB, HALT},
  };

  use super::{AVarSum, AffineVar, Config, Rule, Var};

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

  pub fn parse_num_or_avar<
    'a,
    E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
  >(
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
    Ok((input, ExpTape { left, head, right }))
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

  pub fn parse_end_config<
    'a,
    E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
  >(
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
    let (input, (start, _, end)) =
      (parse_config, tag("\ninto:\n"), parse_end_config).parse(input)?;
    Ok((input, Rule { start, end }))
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

    // #[test]
    // fn test_parse_var_times
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
      let rule_str = "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| \ninto:\nphase: 1  (T, 1) |>F<| (F, 0 + 1*x_0) (T, 1)";
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
}

mod test {
  use nom::{Finish, IResult};

  use crate::{
    rules::parse::{
      parse_avar, parse_avar_gen, parse_config_tape_side, parse_end_config_tape_side, parse_rule,
      parse_tape,
    },
    simulate::TapeHalf,
    turing::{get_machine, Bit},
  };

  use super::*;

  #[test]
  fn affinevar_sub() {
    let three_fifty = AffineVar { n: 50, a: 3, var: Var(0) };
    assert_eq!(three_fifty.sub(6), 68);
    assert_eq!(three_fifty.sub(0), 50);
    let two_x_plus_seven = AffineVar { n: 7, a: 2, var: Var(1) };
    assert_eq!(two_x_plus_seven.sub(19), 45);
    assert_eq!(two_x_plus_seven.sub(3), 13);
  }

  #[test]
  fn affinevar_sub_map() {
    let mut hm = HashMap::new();
    hm.insert(Var(0), 6);
    hm.insert(Var(1), 19);

    let three_fifty = AffineVar { n: 50, a: 3, var: Var(0) };
    let two_x_plus_seven = AffineVar { n: 7, a: 2, var: Var(1) };

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
        right: vec![(Bit(true), AffineVar { n: 0, a: 1, var: Var(0) })],
      },
      end: Config::new_from_avars(
        State(1),
        vec![(Bit(false), AffineVar { n: 0, a: 1, var: Var(0) })],
        Bit(true),
        vec![],
      ),
    };
    let rule2 = Rule {
      start: Config {
        state: State(3),
        left: vec![(Bit(true), AffineVar { n: 0, a: 1, var: Var(0) })],
        head: Bit(true),
        right: vec![],
      },
      end: Config::new_from_avars(
        State(3),
        vec![],
        Bit(true),
        vec![(Bit(true), AffineVar { n: 0, a: 1, var: Var(0) })],
      ),
    };
    assert_eq!(detected_rules, vec![rule1, rule2]);
  }

  #[test]
  fn test_match_var_num() {
    let (_leftover, var) = parse_avar(&"3 + 2*x_0").unwrap();
    assert_eq!(match_var_num(var, 3, false), None);
    assert_eq!(
      match_var_num(var, 5, false),
      Some((Right(0), Some((Var(0), 1))))
    );
    assert_eq!(
      match_var_num(var, 6, false),
      Some((Right(1), Some((Var(0), 1))))
    );
    let (_leftover, var) = parse_avar_gen::<nom::error::Error<&str>>(&"3 + 0*x_0").unwrap();
    assert_eq!(match_var_num(var, 2, false), Some((Left(1), None)));
    assert_eq!(match_var_num(var, 3, false), Some((Right(0), None)));
    assert_eq!(match_var_num(var, 5, false), Some((Right(2), None)));
  }

  fn parse_exact<X>(res: IResult<&str, X>) -> X {
    let (leftover, x) = res.unwrap();
    assert_eq!(leftover, "");
    x
  }

  fn parse_half_tape(input: &str) -> Vec<(Bit, AffineVar)> {
    let mut out = parse_exact(parse_config_tape_side(input));
    out.reverse();
    out
  }

  fn parse_end_half_tape(input: &str) -> Vec<(Bit, AVarSum)> {
    let mut out = parse_exact(parse_end_config_tape_side(input));
    out.reverse();
    out
  }

  #[test]
  fn test_match_rule_tape() {
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 1)");
    assert_eq!(start.len(), 3, "{:?}", start);
    let end: Vec<(Bit, SymbolVar)> = parse_half_tape("(T, 3) (F, 2 + 1*x_0) (T, 3)")
      .into_iter()
      .map(|(b, avar)| (b, avar.into()))
      .collect_vec();
    assert_eq!(end.len(), 3);
    let mut hm = HashMap::new();
    let mb_rtm = match_rule_tape(&mut hm, &start, &end, true);
    assert_eq!(mb_rtm, Some(Leftover(2.into())));

    println!("starting match 2");
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 2)");
    assert_eq!(start.len(), 3, "{:?}", start);
    let end: Vec<(Bit, SymbolVar)> = parse_half_tape("(T, 3) (F, 2 + 1*x_0) (T, 1)")
      .into_iter()
      .map(|(b, avar)| (b, avar.into()))
      .collect_vec();
    assert_eq!(end.len(), 3);
    let mut hm = HashMap::new();
    let mb_rtm = match_rule_tape(&mut hm, &start, &end, true);
    assert_eq!(
      mb_rtm,
      Some(ConsumedEnd((Bit(true), AffineVar::constant(1))))
    );

    let rule_str = "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| 
into:
phase: 1  (T, 1) |>F<| (F, 0 + 1*x_0) (T, 1)";
    let (_leftover, rule) = parse_rule(rule_str).unwrap();
    let tape_str = "(T, 1) |>T<| (T, 7)";
    let (_leftover, mut tape) = parse_tape(tape_str).unwrap();
    let tape_copy = tape.clone();
    println!("app1");
    assert_eq!(
      apply_rule_extra_info(&mut tape, State(3), &rule, true),
      None
    );
    assert_eq!(tape, tape_copy);
    //now we apply the rule to a tape that works
    let tape_str = "(T, 2) |>T<| (T, 7)";
    let output_str = "(T, 1) |>F<| (F, 1) (T, 8)";
    let (_leftover, mut tape) = parse_tape(tape_str).unwrap();
    let (_leftover, output_tape) = parse_tape(output_str).unwrap();
    println!("app2");
    assert_eq!(
      apply_rule(&mut tape, State(3), &rule, true),
      Some(Right(State(1)))
    );
    println!(
      "rule\n{}\nactual tape\n{}\ngoal tape\n{}",
      rule_str, tape, output_tape
    );
    assert_eq!(tape, output_tape);
    //and a different tape
    let tape_str = "(T, 2) (F, 2) (T, 4) |>T<| (T, 7)";
    let output_str = "(T, 2) (F, 1) (T, 1) |>F<| (F, 3) (T, 8)";
    let (_leftover, mut tape) = parse_tape(tape_str).unwrap();
    let (_leftover, output_tape) = parse_tape(output_str).unwrap();
    println!("app3");
    assert_eq!(
      apply_rule(&mut tape, State(3), &rule, true),
      Some(Right(State(1)))
    );
    println!(
      "rule\n{}\nactual tape\n{}\ngoal tape\n{}",
      rule_str, tape, output_tape
    );
    assert_eq!(tape, output_tape);
    //and another
    let tape_str = "(T, 2) (F, 1) (T, 4) |>T<| (T, 7)";
    let output_str = "(T, 3) |>F<| (F, 3) (T, 8)";
    let (_leftover, mut tape) = parse_tape(tape_str).unwrap();
    let (_leftover, output_tape) = parse_tape(output_str).unwrap();
    println!("app4");
    assert_eq!(
      apply_rule(&mut tape, State(3), &rule, true),
      Some(Right(State(1)))
    );
    println!(
      "rule\n{}\nactual tape\n{}\ngoal tape\n{}",
      rule_str, tape, output_tape
    );
    assert_eq!(tape, output_tape);
  }

  /* make a test that using chain rules is the same as not using them
   right now the test fails, because B T -> F R B becomes
   phase: B  |>T<| (T, 0 + 1*x_0)
   into
   phase: B  (F, 0 + 1*x_0) |>F<|
   but the final bit which the head is on should be a T, not an F
   that bug is fixed, but now the test fails because 1 chain step might encompass multiple normal steps, so probably the test should track the number of steps a chain step takes
   or something
  */

  fn simultaneous_steps<S: TapeSymbol>(
    machine: &impl Turing<S>,
    normal_tape: &mut ExpTape<S, u32>,
    mut normal_state: State,
    rule_tape: &mut ExpTape<S, u32>,
    rule_state: State,
    rulebook: &Rulebook<S>,
    step: u32,
    verbose: bool,
  ) -> (State, State) {
    assert_eq!(normal_state, rule_state);
    assert_eq!(normal_tape, rule_tape);
    let new_rule_state = one_rule_step(machine, rule_tape, rule_state, rulebook, step, verbose)
      .expect_right("ran forever?")
      .0;
    let mut num_steps_to_match = 0;

    while (new_rule_state, &mut *rule_tape) != (normal_state, normal_tape) {
      if num_steps_to_match > 20 || normal_state == HALT {
        panic!(
          "machine diverged: {} {}\nvs\n{} {}",
          new_rule_state, rule_tape, normal_state, normal_tape
        );
      }
      normal_state = normal_tape
        .step(normal_state, machine)
        .expect_right("machine is defined");
      num_steps_to_match += 1;
    }
    return (normal_state, new_rule_state);
  }

  fn compare_machine_with_chain<S: TapeSymbol>(machine: &impl Turing<S>, num_steps: u32) {
    let mut normal_tape = ExpTape::new();
    let mut normal_state = START;
    let mut rule_tape = ExpTape::new();
    let mut rule_state = START;
    let chain_rules = detect_chain_rules(machine);
    let mut rulebook = Rulebook::new(machine.num_states());
    rulebook.add_rules(chain_rules);
    for step in 1..num_steps + 1 {
      (normal_state, rule_state) = simultaneous_steps(
        machine,
        &mut normal_tape,
        normal_state,
        &mut rule_tape,
        rule_state,
        &rulebook,
        step,
        false,
      );
    }
  }

  #[test]
  fn chain_steps_is_same() {
    compare_machine_with_chain(&get_machine("sweeper"), 100);
    compare_machine_with_chain(&get_machine("binary_counter"), 100);
  }

  #[test]
  fn svar_eq() {
    assert!(SymbolVar { n: 2, a: 3, var: Var(0) } == SymbolVar { n: 2, a: 3, var: Var(0) });
    assert!(SymbolVar { n: 2, a: 3, var: Var(0) } != SymbolVar { n: 2, a: 4, var: Var(0) });
    assert!(SymbolVar { n: 2, a: 3, var: Var(0) } != SymbolVar { n: 1, a: 3, var: Var(0) });
    assert!(SymbolVar { n: 2, a: 3, var: Var(0) } != SymbolVar { n: 2, a: 3, var: Var(1) });
    //a = 0 is a special case
    assert!(SymbolVar { n: 2, a: 0, var: Var(0) } == SymbolVar { n: 2, a: 0, var: Var(0) });
    assert!(SymbolVar { n: 2, a: 0, var: Var(0) } == SymbolVar { n: 2, a: 0, var: Var(1) });
    assert!(SymbolVar { n: 2, a: 0, var: Var(0) } != SymbolVar { n: 1, a: 0, var: Var(0) });
    assert!(SymbolVar { n: 2, a: 0, var: Var(0) } != SymbolVar { n: 2, a: 3, var: Var(0) });
  }

  #[test]
  fn avar_eq() {
    assert!(AffineVar { n: 2, a: 3, var: Var(0) } == AffineVar { n: 2, a: 3, var: Var(0) });
    assert!(AffineVar { n: 2, a: 3, var: Var(0) } != AffineVar { n: 2, a: 4, var: Var(0) });
    assert!(AffineVar { n: 2, a: 3, var: Var(0) } != AffineVar { n: 1, a: 3, var: Var(0) });
    assert!(AffineVar { n: 2, a: 3, var: Var(0) } != AffineVar { n: 2, a: 3, var: Var(1) });
    //a = 0 is a special case
    assert!(AffineVar { n: 2, a: 0, var: Var(0) } == AffineVar { n: 2, a: 0, var: Var(0) });
    assert!(AffineVar { n: 2, a: 0, var: Var(0) } == AffineVar { n: 2, a: 0, var: Var(1) });
    assert!(AffineVar { n: 2, a: 0, var: Var(0) } != AffineVar { n: 1, a: 0, var: Var(0) });
    assert!(AffineVar { n: 2, a: 0, var: Var(0) } != AffineVar { n: 2, a: 3, var: Var(0) });
  }

  #[test]
  fn test_match_avar_svar() {
    let a5 = AffineVar::constant(5);
    assert_eq!(
      match_avar_svar(a5, SymbolVar::constant(6)),
      Some((Right(SymbolVar::constant(1)), None))
    );
    assert_eq!(
      match_avar_svar(a5, SymbolVar::constant(4)),
      Some((Left(1), None))
    );
    assert_eq!(
      match_avar_svar(a5, SymbolVar { n: 0, a: 1, var: Var(0) }),
      Some((Right(SymbolVar { n: -5, a: 1, var: Var(0) }), None))
    );

    let x = AffineVar { n: 0, a: 1, var: Var(0) };
    let stuff = SymbolVar { n: 3, a: 2, var: Var(1) };
    assert_eq!(
      match_avar_svar(x, stuff),
      Some((Right(SymbolVar::constant(0)), Some((Var(0), stuff))))
    );

    /*
     2x match 6 returns (0, (x -> 3))
     2x match 7 returns (1, (x -> 3))
     2x match a returns None
     2x match 3a returns (a, (x -> a))
     2x match 2a - 1 returns (1, (x -> a-1))
    */
    let two_x = AffineVar { n: 0, a: 2, var: Var(0) };
    assert_eq!(
      match_avar_svar(two_x, SymbolVar::constant(6)),
      Some((
        Right(SymbolVar::constant(0)),
        Some((Var(0), SymbolVar::constant(3)))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x, SymbolVar::constant(7)),
      Some((
        Right(SymbolVar::constant(1)),
        Some((Var(0), SymbolVar::constant(3)))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x, SymbolVar { n: 0, a: 1, var: Var(0) }),
      None
    );
    assert_eq!(
      match_avar_svar(two_x, SymbolVar { n: 0, a: 3, var: Var(0) }),
      Some((
        Right(SymbolVar { n: 0, a: 1, var: Var(0) }),
        Some((Var(0), SymbolVar { n: 0, a: 1, var: Var(0) }))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x, SymbolVar { n: -1, a: 2, var: Var(0) }),
      Some((
        Right(SymbolVar { n: 1, a: 0, var: Var(0) }),
        Some((Var(0), SymbolVar { n: -1, a: 1, var: Var(0) }))
      ))
    );

    /*
     2x+3 match 6 returns (1, (x -> 1))
     2x+3 match 7 returns (0, (x -> 2))
     2x+3 match a returns None
     2x+3 match 2a returns (1, (x -> a-2))
    */
    let (_leftover, two_x_p3) = parse_avar("3 + 2*x_0").unwrap();
    assert_eq!(
      match_avar_svar(two_x_p3, SymbolVar::constant(6)),
      Some((
        Right(SymbolVar::constant(1)),
        Some((Var(0), SymbolVar::constant(1)))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x_p3, SymbolVar::constant(7)),
      Some((
        Right(SymbolVar::constant(0)),
        Some((Var(0), SymbolVar::constant(2)))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x_p3, SymbolVar { n: 0, a: 1, var: Var(0) }),
      None
    );
    assert_eq!(
      match_avar_svar(two_x_p3, SymbolVar { n: 0, a: 2, var: Var(0) }),
      Some((
        Right(SymbolVar::constant(1)),
        Some((Var(0), SymbolVar { n: -2, a: 1, var: Var(0) }))
      ))
    );
    /*

    ??
    2x+3 match 3a returns (a-1, (x -> a-1))
    2x+5 match 3a returns (a-1, (x -> a-2))
    2x+7 match 3a returns (a-3, (x -> a-2)) or (a-1, (x -> a-3))

    5x+4 match 7a returns (2a-4, (x -> a)) or (2a+1, (x -> a-1))
    5x+5 match 7a returns (2a-5, (x -> a)) or (2a, (x -> a-1))

    so the fundamental confusing thing here, is if we want to optimize for the smallest
    amount subtracted from a at any point, this is at least a little bit a global optimization
    problem. like you can either subtract more from one place or the other, and sometimes
    one or the other is better. see examples.

    but I don't think it actually matters to exactly optimize the value subtracted from a.
    because if you set the minimum value of a for the rule to apply slightly too high, you
    only miss a finite number of cases, which you can solve by brute force if the rule is real.

    for even more simplicity you could maybe even say x is only allowed to be sent to
    positive values of a, which I might do later. but you still have to track the minimum value
    of a pretty carefully so it doesn't seem obviously that helpful
    */

    // 2x+3 match 3a returns (a+1, (x -> a-2))
    assert_eq!(
      match_avar_svar(two_x_p3, SymbolVar { n: 0, a: 3, var: Var(0) }),
      Some((
        Right(SymbolVar { n: 1, a: 1, var: Var(0) }),
        Some((Var(0), SymbolVar { n: -2, a: 1, var: Var(0) }))
      ))
    );
  }

  #[test]
  fn prove_rule_test() {
    let machine = get_machine("sweeper");

    let rulebook = Rulebook::chain_rulebook(&machine);

    let non_conserving_rule = parse_rule(
      "phase: A   |>F<| (T, 0 + 1*x_0)
into:
phase: A   |>F<| (T, 1 + 1*x_0)",
    )
    .unwrap()
    .1;
    assert_eq!(
      prove_rule(&machine, non_conserving_rule, &rulebook, 100, -5, true),
      None
    );
    let wrong_conserving_rule = parse_rule(
      "phase: A   |>F<| (T, 0 + 1*x_0) (F, 1)
into:
phase: A   |>F<| (T, 1 + 1*x_0)",
    )
    .unwrap()
    .1;
    assert_eq!(
      prove_rule(&machine, wrong_conserving_rule, &rulebook, 100, -5, true),
      None
    );
    let conserving_rule = parse_rule(
      "phase: A  (F, 1) |>F<| (T, 0 + 1*x_0) (F, 1)
into:
phase: A   |>F<| (T, 1 + 1*x_0) (F, 1)",
    )
    .unwrap()
    .1;
    let obs = prove_rule(&machine, conserving_rule, &rulebook, 100, -5, true);
    let proved_conserving_rule = parse_rule(
      "phase: A  (F, 1) |>F<| (T, 1 + 1*x_0) (F, 1)
into:
phase: A   |>F<| (T, 2 + 1*x_0) (F, 1)",
    )
    .unwrap()
    .1;
    let ans = Some((proved_conserving_rule, RuleProof::DirectSimulation(7)));
    println!("\n\nproved: {}\n", obs.clone().unwrap().0);
    println!("goal: {}\n", ans.clone().unwrap().0);
    assert_eq!(obs, ans);
  }

  #[test]
  fn chain_var_test() {
    let mut hm = HashMap::new();
    let chaining_var = Var(0);
    //(3, 3) -> (3, 3)
    let av3 = AffineVar::constant(3);
    let avs3 = AVarSum::constant(3);
    assert_eq!(
      chain_var(&mut hm, av3, &avs3, chaining_var),
      Some((av3, avs3.clone()))
    );
    //(3, x) -> (3, 3)
    let x = Var(1);
    let av_x = AffineVar { n: 0, a: 1, var: x };
    let avs_x = av_x.into();
    hm.insert(x, 3.into());
    assert_eq!(
      chain_var(&mut hm, av3, &avs_x, chaining_var),
      Some((av3, avs3.clone()))
    );
    //(x, 3) -> (3, 3)
    assert_eq!(
      chain_var(&mut hm, av_x, &AVarSum::constant(3), chaining_var),
      Some((av3, avs3.clone()))
    );
    //(x, x+1) -> (x, x+k)
    let mut avs_x_plus_one = avs_x.clone();
    avs_x_plus_one.n = 1;
    let mut avs_x_plus_cv = avs_x.clone();
    avs_x_plus_cv.add_avar(AffineVar { n: 0, a: 1, var: chaining_var });
    assert_eq!(
      chain_var(&mut hm, av_x, &avs_x_plus_one, chaining_var),
      Some((av_x, avs_x_plus_cv))
    );
    //(2x + 5, 2x+8) -> (2x + 5, 2x+5+3k)
    let av_2x_plus_5 = AffineVar { n: 5, a: 2, var: x };
    let mut avs_2x_plus_8: AVarSum = av_2x_plus_5.into();
    avs_2x_plus_8.add_avar(AffineVar::constant(3));
    let mut avs_2x_plus_5_plus_3k: AVarSum = av_2x_plus_5.into();
    avs_2x_plus_5_plus_3k.add_avar(AffineVar { n: 0, a: 3, var: chaining_var });
    assert_eq!(
      chain_var(&hm, av_2x_plus_5, &avs_2x_plus_8, chaining_var),
      Some((av_2x_plus_5, avs_2x_plus_5_plus_3k))
    );
  }

  #[test]
  fn chain_side_test() {
    // ([], []) -> same
    let start = vec![];
    let end = vec![];
    assert_eq!(chain_side::<Bit>(&start, &end, Var(0)), Some((start, end)));

    // ([(F, 1)], []) -> ([(F, x)], [])
    let start = parse_half_tape("(F, 1)");
    assert_eq!(start.len(), 1);
    let start_out = parse_half_tape("(F, 0 + 1*x_0)");
    assert_eq!(start_out.len(), 1);
    let end = vec![];
    assert_eq!(chain_side(&start, &end, Var(0)), Some((start_out, end)));

    // ([], [(T, 1)]) -> ([], [(T, x)])
    let start = vec![];
    let end = av_to_avs(parse_half_tape("(T, 1)"));
    let end_out = av_to_avs(parse_half_tape("(T, 0 + 1*x_0)"));
    assert_eq!(chain_side(&start, &end, Var(0)), Some((start, end_out)));

    // ([(T, 3), (F, x+1), (T, 2)], '') -> ('', '')
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 2)");
    assert_eq!(start.len(), 3);
    let end = av_to_avs(start.clone());
    assert_eq!(chain_side(&start, &end, Var(0)), Some((start, end)));

    // ([(T, 3), (F, x+1), (T, 1)], [(T, 3), (F, x+2), (T, 3)])
    // ([(T, 3), (F, x+1), (T, 1)], [(T, 3), (F, 1+x+k), (T, 1+2k)])
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 1)");
    assert_eq!(start.len(), 3);
    let end = av_to_avs(parse_half_tape("(T, 3) (F, 2 + 1*x_0) (T, 3)"));
    assert_eq!(end.len(), 3);
    let end_out = parse_end_half_tape("(T, 3) (F, 1 + 1*x_0 + 1*x_1) (T, 1 + 2*x_1)");
    let (start_ans, end_ans) = chain_side(&start, &end, Var(1)).unwrap();
    println!(
      "1 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    // ([(T, 3), (F, x+1), (T, 2)], [(T, 3), (F, x+2), (T, 1)])
    // ([(T, 3), (F, x+1), (T, 1+k)], [(T, 3), (F, 1+x+k), (T, 1)])
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 2)");
    assert_eq!(start.len(), 3);
    let end = parse_end_half_tape("(T, 3) (F, 2 + 1*x_0) (T, 1)");
    assert_eq!(end.len(), 3);
    let start_out = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 1 + 1*x_1)");
    let end_out = parse_end_half_tape("(T, 3) (F, 1 + 1*x_0 + 1*x_1) (T, 1)");
    let (start_ans, end_ans) = chain_side(&start, &end, Var(1)).unwrap();
    println!(
      "2 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start_out, end_out));

    // ([(F, 1), (T, 4)], [(F, 1), (T, 4), (F, 1)])
    // ([(F, 1), (T, 4)], [(F, 1), (T, 4), (F, x)])
    let start = parse_half_tape("(F, 1) (T, 4)");
    assert_eq!(start.len(), 2);
    let end = parse_end_half_tape("(F, 1) (T, 4) (F, 1)");
    assert_eq!(end.len(), 3);
    let end_out = parse_end_half_tape("(F, 1) (T, 4) (F, 0 + 1*x_0)");
    let (start_ans, end_ans) = chain_side(&start, &end, Var(0)).unwrap();
    println!(
      "3 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    // ([(F, 1), (T, 3)], [(F, 1), (T, 4), (F, 1)]) -> None
    let start = parse_half_tape("(F, 1) (T, 3)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(F, 1) (T, 4) (F, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0)), None);

    // ([(F, 1), (T, 4)], [(F, 1), (T, 3), (F, 1)]) -> None
    let start = parse_half_tape("(F, 1) (T, 4)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(F, 1) (T, 3) (F, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0)), None);

    // ([(T, 2), (F, 4)] [(T, 2), (F, 3), (T, 1)]) -> None
    let start = parse_half_tape("(T, 2) (F, 4)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(T, 2) (F, 3) (T, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0)), None);

    // ([(T, 2), (F, 3), (T, 1)] [(T, 2), (F, 4)]) -> None
    let start = parse_half_tape("(T, 2) (F, 3) (T, 1)");
    let end = av_to_avs(parse_half_tape("(T, 2) (F, 4)"));
    assert_eq!(chain_side(&start, &end, Var(0)), None);
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
    chain (x+1, x) (x, 0) + x = n

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
    println!("by chaining, obtained:\n{}", ans);
    assert_eq!(ans, chained_rule);
  }
}
