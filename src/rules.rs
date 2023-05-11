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
  simulate::{
    ExpTape, Signature,
    StepResult::{FellOffTape, Success, UndefinedEdge},
    TapeChange, TapeChangeKind, TapeHalf,
  },
  turing::{
    Bit,
    Dir::{self, L, R},
    Edge, SmallBinMachine, State, TapeSymbol, Trans, Turing, HALT, INFINITE, START,
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

impl Count for AffineVar {
  fn zero() -> Self {
    AffineVar::constant(0)
  }

  fn add(AffineVar { n, a, var }: Self, AffineVar { n: m, a: b, var: var2 }: Self) -> Self {
    //todo oh no this is a mess
    let var_out = match (a, b) {
      (0, 0) => Var(0),
      (_a, 0) => var,
      (0, _b) => var2,
      (_a, _b) => {
        if var != var2 {
          panic!("added incompatible AffineVars")
        } else {
          var
        }
      }
    };
    AffineVar { n: n + m, a: a + b, var: var_out }
  }

  fn mul_const(self, multiplier: u32) -> Self {
    let AffineVar { n, a, var } = self;
    AffineVar { n: n * multiplier, a: a * multiplier, var: var }
  }
}

impl AffineVar {
  pub fn constant(n: u32) -> Self {
    Self { n, a: 0, var: Var(0) }
  }

  pub fn sub<C: Count>(&self, x: C) -> C {
    let &AffineVar { n, a, var: _var } = self;
    // return n + a * x;
    return C::add(n.into(), x.mul_const(a));
  }

  pub fn sub_equation(&self, lhs: Var, rhs: AffineVar) -> AffineVar {
    if self.var == lhs {
      self.sub(rhs)
    } else {
      *self
    }
  }

  pub fn sub_equations(&self, hm: &HashMap<Var, AffineVar>) -> AffineVar {
    match hm.get(&self.var) {
      None => *self,
      Some(&rhs) => self.sub(rhs),
    }
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

  fn from_tape_state(
    state: State,
    ExpTape { left, head, right, tape_end_inf: _ }: ExpTape<S, u32>,
  ) -> Self {
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
        let tape = ExpTape { left, head, right, tape_end_inf: false };
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
        let tape = ExpTape { left, head, right, tape_end_inf: false };
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

impl<S: Display + Copy> Display for Rulebook<S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "rulebook:\n")?;
    for rules_vec in self.1.iter() {
      for rule in rules_vec {
        write!(f, "{}\n", rule)?;
      }
    }
    Ok(())
  }
}

impl<S: TapeSymbol> Rulebook<S> {
  pub fn new(num_states: u8) -> Self {
    let mut sv = smallvec![];
    //todo: multisymbol
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

pub trait Count: Copy + Eq + Hash + Debug + Display + From<u32> {
  fn zero() -> Self;
  fn add(x: Self, y: Self) -> Self;
  fn mul_const(self, n: u32) -> Self;
}

pub trait TapeCount: Count {
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
      println!("num too small")
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

impl Count for u32 {
  fn zero() -> Self {
    0
  }

  fn add(x: Self, y: Self) -> Self {
    x + y
  }

  fn mul_const(self, n: u32) -> Self {
    self * n
  }
}

impl TapeCount for u32 {
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
        assert!(rule.len() <= tape.len(), "{} {}", rule.len(), tape.len());
        // todo change <= to ==
        if rule.len() == tape.len() {
          let ans = ConsumedEnd((rule.get(0).unwrap().0, eat_past_end.into()));
          if verbose {
            println!(
              "didn't match empty and ate past end, so ConsumedEnd: {:?}",
              ans
            );
          }
          return Some(ans);
        } else {
          return None;
        }
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
    Leftover(leftover) if leftover == Count::zero() => remove(tape, rule_len),
    Leftover(leftover) => {
      remove(tape, rule_len - 1);
      tape.last_mut().unwrap().1 = leftover;
    }
  }
}

pub fn size_consumed<S: TapeSymbol, C: TapeCount>(
  rule: &Vec<(S, AffineVar)>,
  hm: &HashMap<Var, C>,
) -> C {
  let mut out = C::zero();
  for (_s, avar) in rule {
    out = C::add(out, avar.sub_map(hm));
  }
  out
}

pub fn append_rule_tape<S: TapeSymbol, C: TapeCount>(
  hm: &HashMap<Var, C>,
  rule: &[(S, AVarSum)],
  tape: &mut Vec<(S, C)>,
  tape_end_inf: bool,
) -> C {
  // the avar is the amount we shrank the tape by, if any
  // the C is the total amount of stuff we pushed onto the tape
  let mut stuff_pushed = C::zero();
  // todo!("stuff pushed update here");
  let slice_to_append = match rule.get(0) {
    None => return C::zero(),
    Some((s, avar)) => match tape.last_mut() {
      None => {
        if *s == S::empty() && tape_end_inf {
          let dropped_off_end = avar.sub_map(hm);
          stuff_pushed = C::add(stuff_pushed, dropped_off_end);
          &rule[1..]
        } else {
          &rule[..]
        }
      }
      Some((t, num)) => {
        if s == t {
          let add_to_end = avar.sub_map(hm);
          stuff_pushed = C::add(stuff_pushed, add_to_end);
          *num = C::add(*num, add_to_end);
          &rule[1..]
        } else {
          &rule[..]
        }
      }
    },
  };
  tape.extend(slice_to_append.iter().map(|(s, avar)| {
    let ans = avar.sub_map(hm);
    stuff_pushed = C::add(stuff_pushed, ans);
    (*s, ans)
  }));
  stuff_pushed
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

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ReadShift {
  pub l: i32,
  pub r: i32,
  pub s: i32,
}

pub const RS_LEFT: ReadShift = ReadShift { l: 0, r: 0, s: -1 };
pub const RS_RIGHT: ReadShift = ReadShift { l: 0, r: 0, s: 1 };

impl ReadShift {
  pub fn normalize(ReadShift { l, r, s }: ReadShift) -> Self {
    // the problem with ReadShift {0, 0, 1} is if you try to cut at the start and end
    // that doesn't work right
    // so you normalize it to {0, 1, 1}
    let new_r = if r - s < 0 {
      assert_eq!(r - s, -1);
      r + 1
    } else {
      r
    };
    let new_l = if l - s > 0 {
      assert_eq!(l - s, 1);
      l - 1
    } else {
      l
    };
    ReadShift { l: new_l, r: new_r, s }
  }

  pub fn combine(
    ReadShift { l, r, s }: ReadShift,
    ReadShift { l: l2, r: r2, s: s2 }: ReadShift,
  ) -> ReadShift {
    /* from the perspective of the first readshift, the second one is effectively shifted
    by s */
    let l2_first_frame = l2 + s;
    let r2_first_frame = r2 + s;
    let l_out = l.min(l2_first_frame);
    let r_out = r.max(r2_first_frame);
    let s_out = s + s2;
    ReadShift { l: l_out, r: r_out, s: s_out }
  }
  pub fn combine_many(inps: &[ReadShift]) -> ReadShift {
    // inps must be nonempty
    let mut out = *inps.get(0).unwrap();
    for &rs in &inps[1..] {
      out = Self::combine(out, rs);
    }
    out
  }

  pub fn rs_in_dir(dir: Dir) -> ReadShift {
    match dir {
      L => RS_LEFT,
      R => RS_RIGHT,
    }
  }

  fn rs_from_cg(
    ConsumeGrow { left_consume, right_consume, left_grow, right_grow }: ConsumeGrow<u32>,
  ) -> ReadShift {
    let lc: i32 = left_consume.try_into().unwrap();
    let l = lc * -1;
    let rc: i32 = right_consume.try_into().unwrap();
    let r = rc;
    let lg: i32 = left_grow.try_into().expect(&format!("lg: {}", left_grow));
    let rg: i32 = right_grow.try_into().unwrap();
    let s = rc - rg;
    let s2 = lg - lc;
    assert_eq!(s, s2, "{} {} {} {}", lc, rc, lg, rg);
    ReadShift { l, r, s }
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ConsumeGrow<C> {
  left_consume: C,
  right_consume: C,
  left_grow: C,
  right_grow: C,
}

pub fn apply_rule_extra_info<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  cur_state: State,
  Rule { start: Config { state, left, head, right }, end }: &Rule<S>,
  verbose: bool,
) -> Option<Either<Var, (State, HashMap<Var, C>, ConsumeGrow<C>)>> {
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
      if !tape.tape_end_inf {
        return None;
      }
      if let None = avar.sub_map_maybe(&hm) {
        return Some(Left(avar.var));
      }
    }
    if let ConsumedEnd((_, avar)) = right_match {
      if !tape.tape_end_inf {
        return None;
      }
      if let None = avar.sub_map_maybe(&hm) {
        return Some(Left(avar.var));
      }
    }
    consume_tape_from_rulematch(&mut tape.left, left_match, left.len());
    consume_tape_from_rulematch(&mut tape.right, right_match, right.len());

    let left_consume = size_consumed(left, &hm);
    let right_consume = size_consumed(right, &hm);
    let left_grow = append_rule_tape(&hm, &end.left, &mut tape.left, tape.tape_end_inf);
    let right_grow = append_rule_tape(&hm, &end.right, &mut tape.right, tape.tape_end_inf);
    tape.head = end.head;

    let cg = ConsumeGrow { left_consume, right_consume, left_grow, right_grow };
    return Some(Right((end.state, hm, cg)));
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
    Some(Right(ans)) => Some(Right(ans.0)),
  }
}

pub fn apply_rules<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  state: State,
  rulebook: &Rulebook<S>,
  verbose: bool,
) -> Option<Either<Var, (State, HashMap<Var, C>, ConsumeGrow<C>)>> {
  let edge = Edge(state, tape.head);
  let rules = rulebook.get_rules(edge);
  for rule in rules {
    match apply_rule_extra_info(tape, state, rule, false) {
      None => (),
      Some(ans) => {
        if verbose {
          println!("rule:\n{}", rule);
        }
        return Some(ans);
      }
    }
  }
  return None;
}
pub enum RuleStepResult<C> {
  VarInfinite(Var),
  RFellOffTape(Dir),
  RSuccess(
    State,
    HashMap<Var, C>,
    // RuleTapeChange,
    Either<ReadShift, ConsumeGrow<C>>,
  ),
}
use RuleStepResult::*;

pub fn one_rule_step<S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<S>,
  exptape: &mut ExpTape<S, C>,
  state: State,
  rulebook: &Rulebook<S>,
  step: u32,
  verbose: bool,
) -> RuleStepResult<C> {
  let (new_state, hm, rs) = match apply_rules(exptape, state, rulebook, false) {
    Some(Left(var)) => return VarInfinite(var),
    Some(Right((state, tc, cg))) => {
      if verbose {
        println!("rule_applied");
      }
      (state, tc, Right(cg))
    }
    None => match exptape.step_extra_info(state, machine) {
      UndefinedEdge(_edge) => unreachable!("machine is defined"),
      FellOffTape(dir) => return RFellOffTape(dir),
      Success(state, rs) => (state, HashMap::default(), Left(rs)),
    },
  };
  if verbose {
    println!("step: {} phase: {} tape: {}", step, new_state, exptape);
  }
  return RSuccess(new_state, hm, rs);
}

pub fn simulate_using_rules<S: TapeSymbol, C: TapeCount>(
  machine: &impl Turing<S>,
  num_steps: u32,
  rulebook: &Rulebook<S>,
  verbose: bool,
) -> (State, u32, ExpTape<S, C>) {
  let mut exptape = ExpTape::new(true);
  let mut state = START;
  for step in 1..num_steps + 1 {
    state = match one_rule_step(machine, &mut exptape, state, rulebook, step, verbose) {
      VarInfinite(_var) => return (INFINITE, step, exptape),
      RFellOffTape(_) => panic!("fell off tape unexpectedly"),
      RSuccess(state, _, _) => state,
    };
    if state == HALT {
      return (HALT, step, exptape);
    }
    // println!("step: {} phase: {} tape: {}", step, state, exptape);
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

fn get_n_rle<S: TapeSymbol>(slice: &[(S, u32)], n: u32) -> Vec<(S, u32)> {
  //gets the last n things from an RLE encoded slice
  let mut num_take = 0;
  let mut current_taken = 0;
  loop {
    if num_take == slice.len() {
      break;
    }
    let (_s, next_int) = slice[(slice.len() - 1) - num_take];
    if current_taken + next_int > n {
      break;
    } else {
      num_take += 1;
      current_taken += next_int;
    }
  }
  let mut out = vec![];
  if current_taken < n {
    if num_take == slice.len() {
      out.push((S::empty(), n - current_taken));
    } else {
      let (s, next_int) = slice[(slice.len() - 1) - num_take];
      assert!(next_int > n - current_taken);
      out.push((s, n - current_taken));
    }
  }
  for i in 0..num_take {
    out.push(slice[slice.len() - num_take + i])
  }
  assert_eq!(n, out.iter().map(|(_, n)| n).sum());
  out
}

fn cut_exptape<S: TapeSymbol>(
  ExpTape { left, head, right, tape_end_inf }: &ExpTape<S, u32>,
  l: i32,
  r: i32,
) -> ExpTape<S, u32> {
  assert!(tape_end_inf);
  assert!(l <= 0, "l should be > 0 {}", l);
  let l_cut = (-1 * l).try_into().unwrap();
  let new_left = get_n_rle(&left, l_cut);

  assert!(r >= 0, "r should be > 0 {}", r);
  let r_cut = r.try_into().unwrap();
  let new_right = get_n_rle(right, r_cut);

  ExpTape {
    left: new_left,
    head: *head,
    right: new_right,
    tape_end_inf: false,
  }
}

fn make_side<S: TapeSymbol>(
  start: &Vec<(S, u32)>,
  end: &Vec<(S, u32)>,
) -> (Vec<(S, AffineVar)>, Vec<(S, AffineVar)>, bool) {
  let (start_idx, end_idx) = match start.len().cmp(&end.len()) {
    Less => (0, end.len() - start.len()),
    Equal => (0, 0),
    Greater => (start.len() - end.len(), 0),
  };

  let mut start_out = start[0..start_idx]
    .into_iter()
    .map(|&(s, n)| (s, n.into()))
    .collect_vec();
  let mut end_out = end[0..end_idx]
    .into_iter()
    .map(|&(s, n)| (s, n.into()))
    .collect_vec();

  let mut var_used = false;
  // for (&s, &e) in zip_eq(start, end) {
  for (&s, &e) in zip_eq(&start[start_idx..], &end[end_idx..]) {
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
  rs: ReadShift,
  verbose: bool,
) -> Vec<Rule<S>> {
  /* we're detecting an additive rule, so any numbers that don't change, we guess don't change
  and any numbers that do change, we guess change by that constant each time
  so we need to
  1) make vectors of the change amount
  2) zip those vectors with the signatures and turn them into configs
  */
  let ReadShift { l, r, s } = ReadShift::normalize(rs);

  assert!(l <= 0, "{:?}", rs);
  assert!(r >= 0, "{:?}", rs);
  let second_last = &history[history.len() - 2];
  let et_in = cut_exptape(&second_last.2, l, r);

  let last = &history[history.len() - 1];
  if verbose {
    println!(
      "detecting rule from step {} to step {}",
      second_last.0, last.0
    );
  }
  let et_out = cut_exptape(&last.2, l - s, r - s);

  if verbose {
    println!("detecting rule from\n{}\nto\n{}", &et_in, &et_out);
  }

  let ExpTape {
    left: end_left_in,
    head: end_head,
    right: end_right_in,
    tape_end_inf: _,
  } = et_out;
  let ExpTape {
    left: start_left_in,
    head: start_head,
    right: start_right_in,
    tape_end_inf: _,
  } = et_in;
  let (start_left, end_left, _var_used_left) = make_side(&start_left_in, &end_left_in);
  let (start_right, end_right, _var_used_right) = make_side(&start_right_in, &end_right_in);
  // if !var_used_left && !var_used_right {
  //   return vec![];
  // }
  let rule = Rule {
    start: Config {
      state: second_last.1,
      left: start_left,
      head: start_head,
      right: start_right,
    },
    end: Config::new_from_avars(last.1, end_left, end_head, end_right),
  };
  vec![rule]
}

pub fn detect_rules<S: TapeSymbol>(
  step: u32,
  state: State,
  exptape: &ExpTape<S, u32>,
  signatures: &mut DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>>,
  readshifts: &Vec<ReadShift>,
  verbose: bool,
) -> Vec<Rule<S>> {
  let cur_sig_vec = &mut signatures[(state, exptape.signature())];
  cur_sig_vec.push((step, state, exptape.clone()));
  if cur_sig_vec.len() > 1 {
    let steps = cur_sig_vec.iter().map(|(s, _, _)| s).collect_vec();
    let second_last_step = *steps[steps.len() - 2] as usize;
    let last_step = *steps[steps.len() - 1] as usize;
    let readshift_range = &readshifts[second_last_step..last_step];
    let readshift = ReadShift::combine_many(readshift_range);
    if verbose {
      println!("detection rs: {:?}", readshift);
    }
    let rules = detect_rule(cur_sig_vec, readshift, false);
    if rules.len() > 0 && verbose {
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

impl Count for SymbolVar {
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
}

impl TapeCount for SymbolVar {
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

impl From<u32> for AVarSum {
  fn from(n: u32) -> Self {
    let mut out = Self::new();
    out.n = n;
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

  fn sub_equation(mut self, lhs: Var, rhs: AffineVar) -> Self {
    let &a = self.var_map.get(lhs);
    self.var_map.remove(&lhs);
    let to_add = rhs.mul_const(a);
    self.add_avar(to_add);
    self
  }

  fn sub_equations(self, new_hm: &HashMap<Var, AffineVar>) -> Self {
    let mut out = Self::constant(self.n);
    for (v, &coeff) in self.var_map.iter() {
      match new_hm.get(v) {
        None => out.add_avar(AffineVar { n: 0, a: coeff, var: *v }),
        Some(rhs) => out.add_avar(rhs.mul_const(coeff)),
      }
    }
    out
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
  ExpTape { mut left, head, mut right, tape_end_inf }: ExpTape<S, SymbolVar>,
) -> (ExpTape<S, SymbolVar>, AVarSum, AVarSum) {
  /* if you're trying to prove a goal tape like
   |>F<| (T, 1 + 1*x_0) (F, 1)
  you will have the problem the (F, 1) gets dropped into the void
  so this processes that into the tape with no empty symbols at the end
  and also what the dropped variables should be
  */
  let left_sum = process_tape_side(&mut left);
  let right_sum = process_tape_side(&mut right);
  (
    ExpTape { left, right, head, tape_end_inf },
    left_sum,
    right_sum,
  )
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
    println!("\nworking to prove rule:\n{}", &rule);
    println!("using rulebook:{}", rulebook);
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
  // let (goal_tape, left_goal_sum, right_goal_sum) = process_goal_tape(goal_tape);

  let mut neg_map: DefaultHashMap<Var, i32> = defaulthashmap! {0};

  for step in 1..prover_steps + 1 {
    let (new_state, hm, _rs) =
      match one_rule_step(machine, &mut proving_tape, state, rulebook, step, verbose) {
        RSuccess(new_state, hm, rs) => (new_state, hm, rs),
        VarInfinite(_) => return None,
        RFellOffTape(_) => return None,
      };
    // if we ever try to grow the tape more than we have already shrunk it, then we
    // immediately fail
    // let ls_res = left_shrink.modify_tapechange(tc.left);
    // let rs_res = right_shrink.modify_tapechange(tc.right);
    // assert_eq!(left_shrink, AVarSum::new());
    // assert_eq!(right_shrink, AVarSum::new());
    // if ls_res.is_none() || rs_res.is_none() {
    //   if verbose {
    //     println!("proving the rule failed because we hit the end of the tape")
    //   }
    //   return None;
    // }
    if verbose {
      // println!("ls: {:?} rs: {:?}", left_shrink, right_shrink);
    }
    if new_state == HALT {
      if verbose {
        println!("proving the rule failed because we transitioned to HALT")
      }
      return None;
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
    if state == goal_state && proving_tape == goal_tape
    // && left_shrink == left_goal_sum
    // && right_shrink == right_goal_sum
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
    println!("proving the rule failed\n");
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

pub fn proving_rules_step<S: TapeSymbol>(
  machine: &impl Turing<S>,
  step: u32,
  mut state: State,
  exptape: &mut ExpTape<S, u32>,
  rulebook: &mut Rulebook<S>,
  signatures: &mut DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>>,
  // tape_diffs: &mut Vec<SmallVec<[TapeDiff; 4]>>,
  readshifts: &mut Vec<ReadShift>,
  verbose: bool,
) -> State {
  if verbose {
    // println!("\nstarting step {}", step);
  }

  let (new_state, _hm, cg_or_rs) =
    match one_rule_step(machine, exptape, state, rulebook, step, verbose) {
      VarInfinite(_var) => {
        if verbose {
          println!("proved machine runs forever using a rule");
        }
        return INFINITE;
      }
      RSuccess(new_state, hm, cg_or_rs) => (new_state, hm, cg_or_rs),
      RFellOffTape(_) => panic!("unexpectedly fell off tape"),
    };
  state = new_state;

  let readshift = cg_or_rs.either(|rs| rs, |cg| ReadShift::rs_from_cg(cg));
  if verbose {
    // println!("rs: {:?}", readshift);
  }
  readshifts.push(readshift);

  if state == HALT {
    return HALT;
  }

  let rules = detect_rules(step, state, &exptape, signatures, &readshifts, false);
  for rule in rules {
    if let Some((final_rule, pf)) = prove_rule(machine, rule, rulebook, 20, -5, false) {
      if pf != DirectSimulation(1) {
        if let Some(chained_rule) = chain_rule(&final_rule) {
          if verbose {
            println!("proved rule:\n{}\nvia proof{:?}", final_rule, pf);
          }
          if verbose {
            println!("chained the proved rule to:\n{}", chained_rule);
          }
          rulebook.add_rule(chained_rule);
        } else {
          if verbose {
            println!(
              "proved rule:\n{}\nvia proof{:?}\nbut could not chain",
              final_rule, pf
            );
          }
        }
        // rulebook.add_rule(final_rule);
      }
    }
  }
  state
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
  let mut exptape = ExpTape::new(true);
  let mut state = START;
  let mut signatures: DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>> =
    defaulthashmap!();
  // let mut tape_diffs = vec![];
  let mut readshifts = vec![];
  for step in 1..num_steps + 1 {
    state = proving_rules_step(
      machine,
      step,
      state,
      &mut exptape,
      rulebook,
      &mut signatures,
      // &mut tape_diffs,
      &mut readshifts,
      verbose,
    );
    if state == INFINITE || state == HALT {
      return (state, step);
    }
    if exptape.numbers_too_large() {
      //put cond about u32s
      println!(
        "warning! gave up on machine {} due to simulating to\nstep: {} phase: {} tape: {}",
        machine.to_compact_format(),
        step,
        state,
        exptape
      );
      return (state, step);
    }
  }
  return (state, num_steps);
}

pub fn aggregate_and_display_proving_res(results: &Vec<(SmallBinMachine, State, u32)>) {
  let mut halt_count = 0;
  let mut inf_count = 0;
  let mut inconclusive_count = 0;
  for (_m, state, _steps) in results {
    match *state {
      HALT => halt_count += 1,
      INFINITE => inf_count += 1,
      _ => inconclusive_count += 1,
    }
  }
  println!(
    "halted: {} infinite: {} inconclusive: {}",
    halt_count, inf_count, inconclusive_count
  );
}

pub fn chain_var(
  hm: &HashMap<Var, SymbolVar>,
  new_hm: &mut HashMap<Var, AffineVar>,
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

  returns: (start, end)
  new_hm is the map which we might modify to contain x or k or whatnot
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
          None
        }
        Ok((&var2, &b)) => {
          if var != var2 || a != b {
            println!("tried to chain {} into {} and couldn't #2", start, end);
            return None;
          }

          if n <= end.n {
            // (ax + n, ax + m) -> (ax + n, ax + n + k*(m - n))
            let mut end_out: AVarSum = start.into();
            let coeff_chain_var = end.n - n;
            if coeff_chain_var > 0 {
              end_out.add_avar(AffineVar { n: 0, a: coeff_chain_var, var: chaining_var });
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
              if new_hm.contains_key(&chaining_var) {
                println!("tried to chain {} into {} and couldn't #3", start, end);
                return None;
              }
              new_hm.insert(chaining_var, AffineVar { n: 0, a: rem, var: start.var });
              Some((start, end_out))
            } else if a == 1 {
              // return None;
              //(x + d + c, x + c) -> (x + d + c, d + c) + x = dk
              let end_out = AVarSum::constant(n);
              // add x = dk to map
              if new_hm.contains_key(&var) {
                dbg!(hm, new_hm);
                println!("tried to chain {} into {} and couldn't #4", start, end);
                return None;
              }
              new_hm.insert(var, AffineVar { n: 0, a: decrease_amt, var: chaining_var });
              Some((start, end_out))
            } else {
              println!("tried to chain {} into {} and couldn't #5", start, end);
              None
            }
          }
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
  match var_used_vec.last() {
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
  chaining_var: Var,
  new_hm: &mut HashMap<Var, AffineVar>,
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
      let ans = (Start, s, avar.times_var(chaining_var)?);
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
          ((End, *end_s, end_v.times_var(chaining_var)?), 0, 1)
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
              AffineVar::from(svar).times_var(chaining_var)?,
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
    let (s_var_out, e_var_out) = chain_var(&hm, new_hm, s_var, e_var, chaining_var)?;
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
  let mut new_hm = HashMap::new();
  let (mut left_start_out, mut left_end_out) =
    chain_side(left_start, left_end, chaining_var, &mut new_hm)?;
  let (mut right_start_out, mut right_end_out) =
    chain_side(right_start, right_end, chaining_var, &mut new_hm)?;
  left_start_out = left_start_out
    .into_iter()
    .map(|(s, avar)| (s, avar.sub_equations(&new_hm)))
    .collect();
  right_start_out = right_start_out
    .into_iter()
    .map(|(s, avar)| (s, avar.sub_equations(&new_hm)))
    .collect();
  left_end_out = left_end_out
    .into_iter()
    .map(|(s, avarsum)| (s, avarsum.sub_equations(&new_hm)))
    .collect();
  right_end_out = right_end_out
    .into_iter()
    .map(|(s, avarsum)| (s, avarsum.sub_equations(&new_hm)))
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
  if new_hm.len() > 1 {
    println!(
      "exciting! chained\n{}\ninto\n{}\n",
      rule,
      ans.clone().unwrap()
    );
  }
  ans
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
      parse_avar, parse_avar_gen, parse_avar_sum, parse_config_tape_side,
      parse_end_config_tape_side, parse_rule, parse_tape,
    },
    simulate::TapeHalf,
    turing::{get_machine, Bit},
    undecided_size_3,
  };

  use super::{parse::parse_tape_side, *};

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

    /* regression test for:
    step: 33 phase: C tape: (T, 1) |>T<| (F, 1) (T, 1) (F, 2) (T, 1)
    rule:
    phase: C  (T, 0 + 1*x_0) |>T<| (F, 2)
    into:
    phase: A  (T, 1 + 1*x_0) |>T<| (F, 1)
    rule_applied
    step: 34 phase: A tape: (T, 2) |>T<| (F, 2) (T, 1) (F, 2) (T, 1)
    */
    println!("app5");
    let rule_str = "phase: C  (T, 0 + 1*x_0) |>T<| (F, 2)
into:
phase: A  (T, 1 + 1*x_0) |>T<| (F, 1)";
    let rule = parse_exact(parse_rule(rule_str));
    let tape_str = "(T, 1) |>T<| (F, 1) (T, 1) (F, 2) (T, 1)";
    let mut tape = parse_exact(parse_tape(tape_str));
    let tape_copy = tape.clone();
    println!("applying {} to \n{}", rule, tape);
    assert_eq!(
      apply_rule_extra_info(&mut tape, State(3), &rule, true),
      None,
      "wrong tape was: {}",
      tape,
    );
    assert_eq!(tape, tape_copy);
  }

  fn simultaneous_step_prove_step<S: TapeSymbol>(
    machine: &impl Turing<S>,
    step: u32,
    normal_tape: &mut ExpTape<S, u32>,
    mut normal_state: State,
    rule_tape: &mut ExpTape<S, u32>,
    rule_state: State,
    rulebook: &mut Rulebook<S>,
    signatures: &mut DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>>,
    // tape_diffs: &mut Vec<SmallVec<[TapeDiff; 4]>>,
    readshifts: &mut Vec<ReadShift>,
    verbose: bool,
  ) -> Option<(State, State)> {
    assert_eq!(normal_state, rule_state);
    assert_eq!(normal_tape, rule_tape);
    let new_rule_state = proving_rules_step(
      machine, step, rule_state, rule_tape, rulebook, signatures, readshifts, verbose,
    );
    if new_rule_state == INFINITE {
      return None;
    }

    let mut num_steps_to_match = 0;

    while (new_rule_state, &mut *rule_tape) != (normal_state, normal_tape) {
      if num_steps_to_match > 300 || normal_state == HALT {
        panic!(
          "machine diverged:\n{} {}\nvs\n{} {}",
          new_rule_state, rule_tape, normal_state, normal_tape
        );
      }
      normal_state = normal_tape
        .step_extra_info(normal_state, machine)
        .expect_success()
        .0;
      num_steps_to_match += 1;
    }
    return Some((normal_state, new_rule_state));
  }

  fn compare_machine_with_proving_rules<S: TapeSymbol>(machine: &impl Turing<S>, num_steps: u32) {
    let mut normal_tape = ExpTape::new(true);
    let mut normal_state = START;
    let mut rule_tape = ExpTape::new(true);
    let mut rule_state = START;
    let mut rulebook = Rulebook::chain_rulebook(machine);
    let mut signatures: DefaultHashMap<(State, Signature<S>), Vec<(u32, State, ExpTape<S, u32>)>> =
      defaulthashmap!();
    // let mut tape_diffs = vec![];
    let mut readshifts = vec![];
    for step in 1..num_steps + 1 {
      (normal_state, rule_state) = match simultaneous_step_prove_step(
        machine,
        step,
        &mut normal_tape,
        normal_state,
        &mut rule_tape,
        rule_state,
        &mut rulebook,
        &mut signatures,
        // &mut tape_diffs,
        &mut readshifts,
        true,
      ) {
        Some(ans) => ans,
        None => return,
      };
    }
  }

  #[test]
  fn prove_rules_is_same_as_not() {
    for m_str in undecided_size_3() {
      println!("working on machine: {}", m_str);
      let machine = SmallBinMachine::from_compact_format(m_str);
      compare_machine_with_proving_rules(&machine, 100);
    }
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

  fn simultaneous_step_chain_step<S: TapeSymbol>(
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
    let rule_result = one_rule_step(machine, rule_tape, rule_state, rulebook, step, verbose);
    let new_rule_state = match rule_result {
      RSuccess(state, _, _) => state,
      VarInfinite(_) => panic!("ran forever?"),
      RFellOffTape(_) => panic!("fell off tape unexpectedly"),
    };

    let mut num_steps_to_match = 0;

    while (new_rule_state, &mut *rule_tape) != (normal_state, normal_tape) {
      if num_steps_to_match > 20 || normal_state == HALT {
        panic!(
          "machine diverged: {} {}\nvs\n{} {}",
          new_rule_state, rule_tape, normal_state, normal_tape
        );
      }
      normal_state = normal_tape
        .step_extra_info(normal_state, machine)
        .expect_success()
        .0;
      num_steps_to_match += 1;
    }
    return (normal_state, new_rule_state);
  }

  fn compare_machine_with_chain<S: TapeSymbol>(machine: &impl Turing<S>, num_steps: u32) {
    let mut normal_tape = ExpTape::new(true);
    let mut normal_state = START;
    let mut rule_tape = ExpTape::new(true);
    let mut rule_state = START;
    let rulebook = Rulebook::chain_rulebook(machine);
    for step in 1..num_steps + 1 {
      (normal_state, rule_state) = simultaneous_step_chain_step(
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
  fn test_add_avar() {
    let lhs = parse_exact(parse_avar("0 + 2*x_0"));
    let rhs = parse_exact(parse_avar("0 + 2*x_0"));
    let ans = parse_exact(parse_avar("0 + 4*x_0"));
    assert_eq!(Count::add(lhs, rhs), ans);

    let lhs = parse_exact(parse_avar("3 + 2*x_0"));
    let rhs = parse_exact(parse_avar("5 + 1*x_0"));
    let ans = parse_exact(parse_avar("8 + 3*x_0"));
    assert_eq!(Count::add(lhs, rhs), ans);

    //regression test
    let lhs = parse_exact(parse_avar("2 + 0*x_0"));
    let rhs = parse_exact(parse_avar("1 + 2*x_1"));
    let ans = parse_exact(parse_avar("3 + 2*x_1"));
    assert_eq!(Count::add(lhs, rhs), ans);
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
  fn test_combine_readshift() {
    let shift_right = ReadShift { l: 0, r: 0, s: 1 };
    let ans = ReadShift { l: 0, r: 1, s: 2 };
    assert_eq!(ReadShift::combine(shift_right, shift_right), ans);
    let shift_left = ReadShift { l: 0, r: 0, s: -1 };
    let ans = ReadShift { l: 0, r: 1, s: 0 };
    assert_eq!(ReadShift::combine(shift_right, shift_left), ans);
    let ans = ReadShift { l: -1, r: 0, s: -2 };
    assert_eq!(ReadShift::combine(shift_left, shift_left), ans);

    let rule_eat = ReadShift { l: -5, r: 4, s: 1 };
    let ans = ReadShift { l: -5, r: 4, s: -2 };
    assert_eq!(
      ReadShift::combine_many(&vec![rule_eat, shift_left, shift_left, shift_left]),
      ans
    );

    let rule_eat_more = ReadShift { l: -2, r: 10, s: -2 };
    let ans = ReadShift { l: -5, r: 11, s: -1 };
    assert_eq!(ReadShift::combine(rule_eat, rule_eat_more), ans);

    let ans = ReadShift { l: -7, r: 10, s: -1 };
    assert_eq!(ReadShift::combine(rule_eat_more, rule_eat), ans);
  }

  #[test]
  fn test_normalize_readshift() {
    let inp = ReadShift { l: 0, r: 0, s: 1 };
    let outp = ReadShift { l: 0, r: 1, s: 1 };
    assert_eq!(ReadShift::normalize(inp), outp);

    let inp = ReadShift { l: -1, r: 0, s: -2 };
    let outp = ReadShift { l: -2, r: 0, s: -2 };
    assert_eq!(ReadShift::normalize(inp), outp);
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
    let mut new_hm = HashMap::new();

    let mut hm = HashMap::new();
    let chaining_var = Var(0);
    //(3, 3) -> (3, 3)
    let av3 = AffineVar::constant(3);
    let avs3 = AVarSum::constant(3);
    assert_eq!(
      chain_var(&hm, &mut new_hm, av3, &avs3, chaining_var),
      Some((av3, avs3.clone()))
    );
    //(3, x) -> (3, 3)
    let x = Var(1);
    let av_x = AffineVar { n: 0, a: 1, var: x };
    let avs_x = av_x.into();
    hm.insert(x, 3.into());
    assert_eq!(
      chain_var(&hm, &mut new_hm, av3, &avs_x, chaining_var),
      Some((av3, avs3.clone()))
    );
    //(x, 3) -> (3, 3)
    assert_eq!(
      chain_var(&hm, &mut new_hm, av_x, &AVarSum::constant(3), chaining_var),
      Some((av3, avs3.clone()))
    );
    //(x, x+1) -> (x, x+k)
    let mut avs_x_plus_one = avs_x.clone();
    avs_x_plus_one.n = 1;
    let mut avs_x_plus_cv = avs_x.clone();
    avs_x_plus_cv.add_avar(AffineVar { n: 0, a: 1, var: chaining_var });
    assert_eq!(
      chain_var(&hm, &mut new_hm, av_x, &avs_x_plus_one, chaining_var),
      Some((av_x, avs_x_plus_cv))
    );
    //(2x + 5, 2x+8) -> (2x + 5, 2x+5+3k)
    let av_2x_plus_5 = AffineVar { n: 5, a: 2, var: x };
    let mut avs_2x_plus_8: AVarSum = av_2x_plus_5.into();
    avs_2x_plus_8.add_avar(AffineVar::constant(3));
    let mut avs_2x_plus_5_plus_3k: AVarSum = av_2x_plus_5.into();
    avs_2x_plus_5_plus_3k.add_avar(AffineVar { n: 0, a: 3, var: chaining_var });
    assert_eq!(
      chain_var(&hm, &mut new_hm, av_2x_plus_5, &avs_2x_plus_8, chaining_var),
      Some((av_2x_plus_5, avs_2x_plus_5_plus_3k))
    );
    assert!(new_hm.is_empty(), "new_hm was not empty: {:?}", new_hm);

    /*
    decreasing vars
    (x+1, x) -> (x+1, 1) + x = k
    (2x + 1, 2x) -> cannot chain
    (2x + 2, 2x) -> (2x + 2, 2) + x = k
    if decrease amt is d and coeff of x is c
    if d == c then easy: (cx + c, cx) -> (cx + c, c) + x = k
    if nd == c for some n, then we set k = nx and get
    (ndx + d, ndx) -> (ndx + d, d) + k = nx
    if d == nc for some n, then maybe x = nk?
    (cx + nc, cx) -> (cx + nc, nc) + x = nk
    which means actually (nck + nc, nc)

    lastly, suppose nd == mc (yikes!)
    (cx + d, cx)
    try setting x = dy?
    (cdy + d, cdy)
    chains to
    (cdy + d, d) + k = cy

    general alg:
    (cx + d, cx)
    let c' = lcm(c, d) = nc = md
    sub x -> ny
    (cny + d, cny) == (mdy + d, mdy)
    chains to
    (mdy + d, d) + k = my

    applying general alg to (3x+1, 3x)
    c' = 3 w/ n=1 m=3
    chains to
    (3x + 1, 1) & k = 3x
    which seems, fine

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

    let mut new_hm = HashMap::new();
    // (x+1, x) chains to (x+1, 1) and k = x
    let av_x_plus_one = AffineVar { n: 1, a: 1, var: x };
    assert_eq!(
      chain_var(&hm, &mut new_hm, av_x_plus_one, &avs_x, chaining_var),
      Some((av_x_plus_one, 1.into()))
    );
    assert_eq!(new_hm.get(&chaining_var), Some(&av_x));

    // (3x+3, 3x+2) chains to (3x+3, 3) and k = 3x
    let mut new_hm = HashMap::new();
    let start = parse_exact(parse_avar("3 + 3*x_0"));
    let end_in = parse_exact(parse_avar_sum("2 + 3*x_0"));
    let end_out = parse_exact(parse_avar_sum("3"));
    let k_ans = parse_exact(parse_avar("0 + 3*x_0"));
    assert_eq!(
      chain_var(&hm, &mut new_hm, start, &end_in, chaining_var),
      Some((start, end_out))
    );
    assert_eq!(new_hm.get(&chaining_var), Some(&k_ans));

    // (4x+2, 4x) chains to (4x+2, 2) and k = 2x
    let mut new_hm = HashMap::new();
    let start = parse_exact(parse_avar("2 + 4*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 4*x_0"));
    let end_out = parse_exact(parse_avar_sum("2"));
    let k_ans = parse_exact(parse_avar("0 + 2*x_0"));
    assert_eq!(
      chain_var(&hm, &mut new_hm, start, &end_in, chaining_var),
      Some((start, end_out))
    );
    assert_eq!(new_hm.get(&chaining_var), Some(&k_ans));

    // (2x, 2x) chains to (2x, 2x)
    let mut new_hm = HashMap::new();
    let start = parse_exact(parse_avar("0 + 2*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 2*x_0"));
    let end_out = parse_exact(parse_avar_sum("0 + 2*x_0"));
    assert_eq!(
      chain_var(&hm, &mut new_hm, start, &end_in, chaining_var),
      Some((start, end_out))
    );
    assert_eq!(new_hm.get(&chaining_var), None);

    // (2x, x) chains to None
    let mut new_hm = HashMap::new();
    let start = parse_exact(parse_avar("0 + 2*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 1*x_0"));
    assert_eq!(
      chain_var(&hm, &mut new_hm, start, &end_in, chaining_var),
      None
    );
    assert!(new_hm.is_empty(), "new_hm was not empty: {:?}", new_hm);
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
    let mut new_hm = HashMap::new();
    let start = parse_exact(parse_avar("2 + 1*x_0"));
    let end_in = parse_exact(parse_avar_sum("0 + 1*x_0"));
    let end_out = parse_exact(parse_avar_sum("2"));
    let x_ans = parse_exact(parse_avar("0 + 2*x_1"));
    assert_eq!(
      chain_var(&hm, &mut new_hm, start, &end_in, chaining_var),
      Some((start, end_out))
    );
    assert_eq!(new_hm.get(&Var(0)), Some(&x_ans));

    // (x+4, x+1) -> (3k+4, 4) x = 3k
    let mut new_hm = HashMap::new();
    let start = parse_exact(parse_avar("4 + 1*x_0"));
    let end_in = parse_exact(parse_avar_sum("1 + 1*x_0"));
    let end_out = parse_exact(parse_avar_sum("4"));
    let x_ans = parse_exact(parse_avar("0 + 3*x_1"));
    assert_eq!(
      chain_var(&hm, &mut new_hm, start, &end_in, chaining_var),
      Some((start, end_out))
    );
    assert_eq!(new_hm.get(&Var(0)), Some(&x_ans));

    // (x+9, x+2) -> (7k+9, 9) x = 7k
    let mut new_hm = HashMap::new();
    let start = parse_exact(parse_avar("9 + 1*x_0"));
    let end_in = parse_exact(parse_avar_sum("2 + 1*x_0"));
    let end_out = parse_exact(parse_avar_sum("9"));
    let x_ans = parse_exact(parse_avar("0 + 7*x_1"));
    assert_eq!(
      chain_var(&hm, &mut new_hm, start, &end_in, chaining_var),
      Some((start, end_out))
    );
    assert_eq!(new_hm.get(&Var(0)), Some(&x_ans));
  }

  #[test]
  fn chain_side_test() {
    let mut new_hm = HashMap::new();
    // ([], []) -> same
    let start = vec![];
    let end = vec![];
    assert_eq!(
      chain_side::<Bit>(&start, &end, Var(0), &mut new_hm),
      Some((start, end))
    );

    // ([(F, 1)], []) -> ([(F, x)], [])
    let start = parse_half_tape("(F, 1)");
    assert_eq!(start.len(), 1);
    let start_out = parse_half_tape("(F, 0 + 1*x_0)");
    assert_eq!(start_out.len(), 1);
    let end = vec![];
    assert_eq!(
      chain_side(&start, &end, Var(0), &mut new_hm),
      Some((start_out, end))
    );

    // ([], [(T, 1)]) -> ([], [(T, x)])
    let start = vec![];
    let end = av_to_avs(parse_half_tape("(T, 1)"));
    let end_out = av_to_avs(parse_half_tape("(T, 0 + 1*x_0)"));
    assert_eq!(
      chain_side(&start, &end, Var(0), &mut new_hm),
      Some((start, end_out))
    );

    // ([(T, 3), (F, x+1), (T, 2)], '') -> ('', '')
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 2)");
    assert_eq!(start.len(), 3);
    let end = av_to_avs(start.clone());
    assert_eq!(
      chain_side(&start, &end, Var(0), &mut new_hm),
      Some((start, end))
    );

    // ([(T, 3), (F, x+1), (T, 1)], [(T, 3), (F, x+2), (T, 3)])
    // ([(T, 3), (F, x+1), (T, 1)], [(T, 3), (F, 1+x+k), (T, 1+2k)])
    let start = parse_half_tape("(T, 3) (F, 1 + 1*x_0) (T, 1)");
    assert_eq!(start.len(), 3);
    let end = av_to_avs(parse_half_tape("(T, 3) (F, 2 + 1*x_0) (T, 3)"));
    assert_eq!(end.len(), 3);
    let end_out = parse_end_half_tape("(T, 3) (F, 1 + 1*x_0 + 1*x_1) (T, 1 + 2*x_1)");
    let (start_ans, end_ans) = chain_side(&start, &end, Var(1), &mut new_hm).unwrap();
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
    let (start_ans, end_ans) = chain_side(&start, &end, Var(1), &mut new_hm).unwrap();
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
    let (start_ans, end_ans) = chain_side(&start, &end, Var(0), &mut new_hm).unwrap();
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
    assert_eq!(chain_side(&start, &end, Var(0), &mut new_hm), None);

    // ([(F, 1), (T, 4)], [(F, 1), (T, 3), (F, 1)]) -> None
    let start = parse_half_tape("(F, 1) (T, 4)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(F, 1) (T, 3) (F, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0), &mut new_hm), None);

    // ([(T, 2), (F, 4)] [(T, 2), (F, 3), (T, 1)]) -> None
    let start = parse_half_tape("(T, 2) (F, 4)");
    assert_eq!(start.len(), 2, "{:?}", start);
    let end = av_to_avs(parse_half_tape("(T, 2) (F, 3) (T, 1)"));
    assert_eq!(end.len(), 3);
    assert_eq!(chain_side(&start, &end, Var(0), &mut new_hm), None);

    // ([(T, 2), (F, 3), (T, 1)] [(T, 2), (F, 4)]) -> None
    let start = parse_half_tape("(T, 2) (F, 3) (T, 1)");
    let end = av_to_avs(parse_half_tape("(T, 2) (F, 4)"));
    assert_eq!(chain_side(&start, &end, Var(0), &mut new_hm), None);

    assert!(new_hm.is_empty(), "new_hm was not empty: {:?}", new_hm);

    let chain_var = Var(1);
    // (F, 1) (T, 4) (F, x+1) -> (F, 1) (T, 4) (F, x)
    // (F, 1) (T, 4) (F, x+1) -> (F, 1) (T, 4) (F, 1)
    // k = x
    let mut new_hm = HashMap::new();
    let start = parse_half_tape("(F, 1) (T, 4) (F, 1 + 1*x_0)");
    let end = parse_end_half_tape("(F, 1) (T, 4) (F, 0 + 1*x_0)");
    let end_out = parse_end_half_tape("(F, 1) (T, 4) (F, 1)");
    let (start_ans, end_ans) = chain_side(&start, &end, chain_var, &mut new_hm).unwrap();
    println!(
      "4 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    let chain_var_rhs = AffineVar { n: 0, a: 1, var: Var(0) };
    assert_eq!(new_hm.get(&Var(1)), Some(&chain_var_rhs));

    // (F, 1) (T, 4) (F, x+2) -> (F, 1) (T, 4) (F, x)
    // (F, 1) (T, 4) (F, x+2) -> (F, 1) (T, 4) (F, 2)
    // x = 2k
    let mut new_hm = HashMap::new();
    let start = parse_half_tape("(F, 1) (T, 4) (F, 2 + 1*x_0)");
    let end = parse_end_half_tape("(F, 1) (T, 4) (F, 0 + 1*x_0)");
    let end_out = parse_end_half_tape("(F, 1) (T, 4) (F, 2)");
    let (start_ans, end_ans) = chain_side(&start, &end, chain_var, &mut new_hm).unwrap();
    println!(
      "5 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    let x_0_rhs = AffineVar { n: 0, a: 2, var: chain_var };
    assert_eq!(new_hm.get(&Var(0)), Some(&x_0_rhs));

    // (T, 4) (F, x+4) (T, 3) -> (T, 4) (F, x+1) (T, 3)
    // (T, 4) (F, x+3) (T, 3) -> (T, 4) (F, 4) (T, 3)
    // x = 3k
    let mut new_hm = HashMap::new();
    let start = parse_half_tape("(T, 4) (F, 4 + 1*x_0) (T, 3)");
    let end = parse_end_half_tape("(T, 4) (F, 1 + 1*x_0) (T, 3)");
    let end_out = parse_end_half_tape("(T, 4) (F, 4) (T, 3)");
    let (start_ans, end_ans) = chain_side(&start, &end, chain_var, &mut new_hm).unwrap();
    println!(
      "6 got ans\n{}\ninto\n{}",
      TapeHalf(Dir::R, &start_ans),
      TapeHalf(Dir::R, &end_ans)
    );
    assert_eq!((start_ans, end_ans), (start, end_out));

    let x_0_rhs = AffineVar { n: 0, a: 3, var: chain_var };
    assert_eq!(new_hm.get(&Var(0)), Some(&x_0_rhs));
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
    let chained_rule = parse_exact(parse_rule(
      "phase: B  (T, 1 + 1*x_0) (F, 1) |>F<| (T, 0 + 1*x_0)
into:
phase: B  (T, 1) (F, 1) |>F<| (T, 0 + 2*x_0)",
    ));
    let ans = chain_rule(&rule).unwrap();
    println!("test 2: by chaining, obtained:\n{}", ans);
    assert_eq!(ans, chained_rule);

    let rule = parse_exact(parse_rule(
      "phase: C  (T, 2 + 1*x_0) |>T<| (T, 0 + 1*x_0)
into:
phase: C  (T, 0 + 1*x_0) |>T<| (T, 2 + 1*x_0)",
    ));
    let chained_rule = parse_exact(parse_rule(
      "phase: C  (T, 2 + 2*x_1) |>T<| (T, 0 + 2*x_1)
into:
phase: C  (T, 2) |>T<| (T, 0 + 4*x_1)",
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
  }

  #[test]
  fn get_n_rle_test() {
    let tape_half = parse_exact(parse_tape_side("(T, 3) (F, 5) (T, 1) (F, 6) (T, 2)"));

    let ans1 = parse_exact(parse_tape_side("(F, 6) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 8), ans1);

    let ans1 = parse_exact(parse_tape_side("(F, 5) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 7), ans1);

    let ans1 = parse_exact(parse_tape_side("(F, 1) (T, 1) (F, 6) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 10), ans1);

    let ans1 = parse_exact(parse_tape_side("(F, 3) (T, 3) (F, 5) (T, 1) (F, 6) (T, 2)"));
    assert_eq!(get_n_rle(&tape_half, 20), ans1);
  }
}
