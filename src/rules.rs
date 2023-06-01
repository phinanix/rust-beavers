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

use crate::{
  chain::rule_runs_forever_if_consumes_all,
  simulate::{one_rule_step, RuleStepResult::*},
  tape::ExpTape,
  turing::{
    Dir::{self, L, R},
    Edge, State, TapeSymbol, Trans, Turing, HALT,
  },
};
use defaultmap::{defaulthashmap, DefaultHashMap};
use either::Either::{self, Left, Right};
use itertools::{chain, Itertools};

use smallvec::{smallvec, SmallVec};
use std::hash::Hash;
use std::{
  collections::{HashMap, HashSet},
  iter::zip,
  ops::Add,
  vec,
};
use std::{
  fmt::{Debug, Display},
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

//each rule has a bool, which is whether this rule applies forever if it consumes all
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Rulebook<S>(u8, SmallVec<[Vec<(Rule<S>, bool)>; 14]>);

impl<S: Display + Copy> Display for Rulebook<S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "rulebook:\n")?;
    for rules_vec in self.1.iter() {
      for (rule, _) in rules_vec {
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
    let consumes_all = rule_runs_forever_if_consumes_all(&rule);
    if consumes_all {
      dbg!(&rule);
    }
    self.1[rule.start_edge_index()].push((rule, consumes_all));
  }

  pub fn add_rules(&mut self, rules: Vec<Rule<S>>) {
    for rule in rules {
      self.add_rule(rule);
    }
  }
  pub fn get_rules(&self, edge: Edge<S>) -> &Vec<(Rule<S>, bool)> {
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
  fn match_avar(
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
// what you would do here is have TapeCount require AddAssign

pub fn match_avar_num(
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
  fn match_avar(
    avar: AffineVar,
    count: Self,
    verbose: bool,
  ) -> Option<(Either<u32, Self>, Option<(Var, Self)>)> {
    match_avar_num(avar, count, verbose)
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
    let (new_leftover, mb_new_var) = C::match_avar(avar, num, verbose)?;

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
  // the C is the total amount of stuff we pushed onto the tape
  let mut stuff_pushed = C::zero();
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

  pub fn rs_from_cg(
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
  rule @ Rule { start: Config { state, left, head, right }, end }: &Rule<S>,
  applies_forever: bool,
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
    let old_tape = tape.clone();
    consume_tape_from_rulematch(&mut tape.left, left_match, left.len());
    consume_tape_from_rulematch(&mut tape.right, right_match, right.len());

    let rule_forever =
      applies_forever && tape.left.is_empty() && tape.right.is_empty() && tape.tape_end_inf;

    let left_consume = size_consumed(left, &hm);
    let right_consume = size_consumed(right, &hm);
    let left_grow = append_rule_tape(&hm, &end.left, &mut tape.left, tape.tape_end_inf);
    let right_grow = append_rule_tape(&hm, &end.right, &mut tape.right, tape.tape_end_inf);
    tape.head = end.head;

    let cg = ConsumeGrow { left_consume, right_consume, left_grow, right_grow };
    if rule_forever {
      println!(
        "proved a machine runs forever using applies forever!\nprev_tape: {}\nrule:\n{}\nnew_tape:\n{}",
        old_tape,
        rule,
        tape
      );
      assert!(false);
      return Some(Left(get_newest_var(&rule)));
    }
    return Some(Right((end.state, hm, cg)));
  } else {
    return None;
  }
}

pub fn apply_rule<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  cur_state: State,
  rule: &Rule<S>,
  applies_forever: bool,
  verbose: bool,
) -> Option<Either<Var, State>> {
  match apply_rule_extra_info(tape, cur_state, rule, applies_forever, verbose) {
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
  for (rule, applies_forever) in rules {
    match apply_rule_extra_info(tape, state, rule, *applies_forever, false) {
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
  fn match_avar(
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
    SymbolVar { n: i32::try_from(n).unwrap(), a, var }
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
  let svar_rhs = SymbolVar { n: integer_in_x, a: coeff_a_in_x, var: svar.var };
  if svar_rhs == SymbolVar::zero() {
    None
  } else {
    Some((Right(svar), Some((avar, svar_rhs))))
  }
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

  pub fn constant(n: u32) -> Self {
    AVarSum { n, var_map: defaulthashmap! {0} }
  }

  fn sub_equation(mut self, lhs: Var, rhs: AffineVar) -> Self {
    let &a = self.var_map.get(lhs);
    self.var_map.remove(&lhs);
    let to_add = rhs.mul_const(a);
    self.add_avar(to_add);
    self
  }

  pub fn sub_equations(self, new_hm: &HashMap<Var, AffineVar>) -> Self {
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

  pub fn add_avar(&mut self, AffineVar { n, a, var }: AffineVar) {
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

  pub fn times_var(&self, var: Var) -> Option<AVarSum> {
    if self.var_map.len() > 0 {
      return None;
    }
    return Some(AffineVar { n: 0, a: self.n, var }.into());
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

  let mut neg_map: DefaultHashMap<Var, i32> = defaulthashmap! {0};

  for step in 1..prover_steps + 1 {
    let (new_state, hm, _rs) =
      match one_rule_step(machine, &mut proving_tape, state, rulebook, step, verbose) {
        RSuccess(new_state, hm, rs) => (new_state, hm, rs),
        VarInfinite(_) => return None,
        RFellOffTape(_, _) => return None,
      };
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
    if state == goal_state && proving_tape == goal_tape {
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

#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    parse::{parse_avar, parse_exact, parse_half_tape, parse_rule, parse_tape},
    turing::{Bit, START},
    turing_examples::get_machine,
  };

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
    assert_eq!(match_avar_num(var, 3, false), None);
    assert_eq!(
      match_avar_num(var, 5, false),
      Some((Right(0), Some((Var(0), 1))))
    );
    assert_eq!(
      match_avar_num(var, 6, false),
      Some((Right(1), Some((Var(0), 1))))
    );
    let (_leftover, var) = parse_avar(&"3 + 0*x_0").unwrap();
    assert_eq!(match_avar_num(var, 2, false), Some((Left(1), None)));
    assert_eq!(match_avar_num(var, 3, false), Some((Right(0), None)));
    assert_eq!(match_avar_num(var, 5, false), Some((Right(2), None)));
    let two_x_p3 = parse_exact(parse_avar("3 + 2*x_0"));
    assert_eq!(match_avar_num(two_x_p3, 3, false), None);
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

    println!("starting match 3");
    let start = parse_half_tape("(T, 2 + 1*x_0)");
    assert_eq!(start.len(), 1, "{:?}", start);
    let end: Vec<(Bit, SymbolVar)> = parse_half_tape("(T, 2)")
      .into_iter()
      .map(|(b, avar)| (b, avar.into()))
      .collect_vec();
    assert_eq!(end.len(), 1);
    let mut hm = HashMap::new();
    let mb_rtm = match_rule_tape(&mut hm, &start, &end, true);
    assert_eq!(mb_rtm, None);

    let rule_str = "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| 
into:
phase: 1  (T, 1) |>F<| (F, 0 + 1*x_0) (T, 1)";
    let (_leftover, rule) = parse_rule(rule_str).unwrap();
    let tape_str = "(T, 1) |>T<| (T, 7)";
    let (_leftover, mut tape) = parse_tape(tape_str).unwrap();
    let tape_copy = tape.clone();
    println!("app1");
    assert_eq!(
      apply_rule_extra_info(
        &mut tape,
        State(3),
        &rule,
        rule_runs_forever_if_consumes_all(&rule),
        true
      ),
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
      apply_rule(
        &mut tape,
        State(3),
        &rule,
        rule_runs_forever_if_consumes_all(&rule),
        true
      ),
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
      apply_rule(
        &mut tape,
        State(3),
        &rule,
        rule_runs_forever_if_consumes_all(&rule),
        true
      ),
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
      apply_rule(
        &mut tape,
        State(3),
        &rule,
        rule_runs_forever_if_consumes_all(&rule),
        true
      ),
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
      apply_rule_extra_info(
        &mut tape,
        State(3),
        &rule,
        rule_runs_forever_if_consumes_all(&rule),
        true
      ),
      None,
      "wrong tape was: {}",
      tape,
    );
    assert_eq!(tape, tape_copy);
  }

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
      RFellOffTape(_, _) => panic!("fell off tape unexpectedly"),
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
    let (leftover, two_x_p3) = parse_avar("3 + 2*x_0").unwrap();
    assert_eq!(leftover.len(), 0);
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

    // 2x+3 match 3
    let ans = match_avar_svar(two_x_p3, SymbolVar { n: 3, a: 0, var: Var(0) });
    assert_eq!(ans, None);
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
}
