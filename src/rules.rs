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
  simulate::{ExpTape, Signature},
  turing::{
    Bit,
    Dir::{L, R},
    Edge, State, TapeSymbol, Trans, Turing, HALT, START,
  },
};
use defaultmap::{defaulthashmap, DefaultHashMap};
use either::Either::{Left, Right};
use itertools::{chain, Itertools};
use proptest::{prelude::*, sample::select};
use smallvec::{smallvec, SmallVec};
use std::hash::Hash;
use std::{cmp::Ordering::*, collections::HashMap, iter::zip};
use std::{
  fmt::{Debug, Display, Write},
  ops::AddAssign,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
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

impl AffineVar {
  pub fn constant(n: u32) -> Self {
    Self { n, a: 0, var: Var(0) }
  }

  pub fn sub<C: TapeCount>(&self, x: C) -> C {
    let &AffineVar { n, a, var: _var } = self;
    // return n + a * x;
    return C::add(n.into(), x.mul_const(a));
  }

  pub fn sub_map<C: TapeCount>(&self, hm: &HashMap<Var, C>) -> C {
    let &x = hm.get(&self.var).unwrap();
    self.sub(x)
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

// much like Tape / ExpTape, the *last* thing in the Vec is the closest to the head,
// for both left and right
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Config<S> {
  pub state: State,
  pub left: Vec<(S, AffineVar)>,
  pub head: S,
  pub right: Vec<(S, AffineVar)>,
}

impl<S: Display + Copy> Display for Config<S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "phase: {}  ", self.state)?;
    for &(s, v) in self.left.iter() {
      write!(f, "({}, {}) ", s, v)?;
    }
    write!(f, "|>{}<|", self.head)?;
    for &(s, v) in self.right.iter().rev() {
      write!(f, " ({}, {})", s, v)?;
    }
    Ok(())
  }
}

impl<S> Config<S> {
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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Rule<S> {
  pub start: Config<S>,
  pub end: Config<S>,
}

impl<S: Display + Copy> Display for Rule<S> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}\ninto\n{}", self.start, self.end)
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

  pub fn add_rules(&mut self, rules: Vec<Rule<S>>) {
    for rule in rules {
      self.add_rule(rule);
    }
  }
  pub fn get_rules(&self, edge: Edge<S>) -> &Vec<Rule<S>> {
    &self.1[edge.edge_index()]
  }
}

pub trait TapeCount: Copy + Eq + Hash + Debug + Display + From<u32> {
  fn zero() -> Self;
  fn add(x: Self, y: Self) -> Self;
  fn mul_const(self, n: u32) -> Self;
  fn match_var(avar: AffineVar, count: Self, verbose: bool) -> Option<(Self, Option<(Var, Self)>)>;
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
) -> Option<(u32, Option<(Var, u32)>)> {
  // returns the num left on the tape, and what to send the var to.
  if num < n {
    if verbose {
      println!("num")
    };
    return None;
  }
  num -= n;
  if a == 0 {
    return Some((num, None));
  }
  if num < a {
    return None;
  } // sending var to 1 would be too big
  Some((num % a, Some((var, num / a))))
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

  fn match_var(avar: AffineVar, count: Self, verbose: bool) -> Option<(Self, Option<(Var, Self)>)> {
    match_var_num(avar, count, verbose)
  }

  fn sub_one(self) -> Self {
    self - 1
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuleTapeMatch<C> {
  ConsumedEnd,
  Leftover(C),
}
use RuleTapeMatch::*;

pub fn match_rule_tape<S: TapeSymbol, C: TapeCount>(
  hm: &mut HashMap<Var, C>,
  rule: &[(S, AffineVar)],
  tape: &[(S, C)],
  verbose: bool,
) -> Option<RuleTapeMatch<C>> {
  // if rule applies, returns
  // 0: how much of the last elt is leftover
  // 1: how many elements
  // else returns none
  let mut leftover = C::zero();
  if rule.len() > tape.len() + 1 {
    if verbose {
      println!("rule too long")
    };
    return None;
  };

  let mut last_elt_empty_tape = false;
  if rule.len() == tape.len() + 1 {
    let last_rule_pair = rule.first().unwrap();
    if last_rule_pair.0 == S::empty() {
      //we can match the empty characters implicitly represented by the end of the tape
      if verbose {
        println!(
          "matched {}, {} to empty",
          last_rule_pair.0, last_rule_pair.1
        )
      };
      last_elt_empty_tape = true;
    } else {
      if verbose {
        println!("rule too long")
      };
      return None;
    }
  }
  let rule_slice_start = if last_elt_empty_tape { 1 } else { 0 };
  for (&(rule_symbol, avar), &(tape_symbol, num)) in
    zip(rule[rule_slice_start..].iter().rev(), tape.iter().rev())
  {
    if leftover != C::zero() {
      if verbose {
        println!("some bits leftover")
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
  if last_elt_empty_tape {
    if leftover != C::zero() {
      return None;
    } else {
      return Some(ConsumedEnd);
    }
  } else {
    return Some(Leftover(leftover));
  }
}

pub fn remove<T>(vec: &mut Vec<T>, to_remove: usize) {
  vec.truncate(vec.len() - to_remove)
}

pub fn consume_tape_from_rulematch<S: TapeSymbol, C: TapeCount>(
  tape: &mut Vec<(S, C)>,
  tape_match: RuleTapeMatch<C>,
  rule_len: usize,
) {
  match tape_match {
    ConsumedEnd => remove(tape, rule_len - 1),
    Leftover(leftover) if leftover == TapeCount::zero() => remove(tape, rule_len),
    Leftover(leftover) => {
      remove(tape, rule_len - 1);
      tape.last_mut().unwrap().1 = leftover;
    }
  }
}

pub fn append_rule_tape<S: TapeSymbol, C: TapeCount>(
  hm: &HashMap<Var, C>,
  rule: &[(S, AffineVar)],
  tape: &mut Vec<(S, C)>,
) {
  let slice_to_append = match rule.get(0) {
    None => return,
    Some((s, avar)) => match tape.last_mut() {
      None => &rule[..],
      Some((t, num)) => {
        if s == t {
          *num = C::add(*num, avar.sub_map(hm));
          &rule[1..]
        } else {
          &rule[..]
        }
      }
    },
  };
  tape.extend(
    slice_to_append
      .iter()
      .map(|&(s, avar)| (s, avar.sub_map(hm))),
  );
}

pub fn apply_rule_hm<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  cur_state: State,
  Rule { start: Config { state, left, head, right }, end }: &Rule<S>,
  verbose: bool,
) -> Option<(State, HashMap<Var, C>)> {
  if cur_state == *state && tape.head == *head {
    let mut hm = HashMap::new();
    if verbose {
      println!("left")
    };
    let left_match = match_rule_tape(&mut hm, left, &tape.left, verbose)?;
    if verbose {
      println!("right")
    };
    let right_match = match_rule_tape(&mut hm, right, &tape.right, verbose)?;
    if verbose {
      println!("succeeded")
    };
    consume_tape_from_rulematch(&mut tape.left, left_match, left.len());
    consume_tape_from_rulematch(&mut tape.right, right_match, right.len());
    append_rule_tape(&hm, &end.left, &mut tape.left);
    append_rule_tape(&hm, &end.right, &mut tape.right);
    tape.head = end.head;
    return Some((end.state, hm));
  } else {
    return None;
  }
}

pub fn apply_rule<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  cur_state: State,
  rule: &Rule<S>,
  verbose: bool,
) -> Option<State> {
  match apply_rule_hm(tape, cur_state, rule, verbose) {
    None => None,
    Some((s, _hm)) => Some(s),
  }
}

pub fn apply_rules<S: TapeSymbol, C: TapeCount>(
  tape: &mut ExpTape<S, C>,
  state: State,
  rulebook: &Rulebook<S>,
  verbose: bool,
) -> Option<(State, HashMap<Var, C>)> {
  let edge = Edge(state, tape.head);
  let rules = rulebook.get_rules(edge);
  for rule in rules {
    match apply_rule_hm(tape, state, rule, verbose) {
      None => (),
      Some((new_state, hm)) => return Some((new_state, hm)),
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
) -> (State, HashMap<Var, C>) {
  let (new_state, hm) = match apply_rules(exptape, state, rulebook, false) {
    Some(res) => {
      println!("rule_applied");
      res
    }
    None => match exptape.step(state, machine) {
      Left(_edge) => unreachable!("machine is defined"),
      Right(state) => (state, HashMap::default()),
    },
  };
  if verbose {
    println!("step: {} phase: {} tape: {}", step, new_state, exptape);
  }
  return (new_state, hm);
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
    state = one_rule_step(machine, &mut exptape, state, rulebook, step, verbose).0;
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
) -> (Vec<(S, AffineVar)>, Vec<(S, AffineVar)>, bool) {
  assert_eq!(start.len(), end.len());
  let mut start_out = vec![];
  let mut end_out = vec![];
  let mut var_used = false;
  for (&s, &e) in zip(start, end) {
    let (s_var, e_var, was_var) = collate(s, e);
    var_used = var_used || was_var;
    start_out.push(s_var);
    end_out.push(e_var);
  }
  (start_out, end_out, var_used)
}

pub fn detect_rule<S: TapeSymbol>(history: &Vec<(u32, State, ExpTape<S, u32>)>) -> Vec<Rule<S>> {
  /* we're detecting an additive rule, so any numbers that don't change, we guess don't change
  and any numbers that do change, we guess change by that constant each time
  so we need to
  1) make vectors of the change amount
  2) zip those vectors with the signatures and turn them into configs
  */
  let second_last = &history[history.len() - 2];
  let last = &history[history.len() - 1];
  let (start_left, end_left, var_used_left) = make_side(&second_last.2.left, &last.2.left);
  let (start_right, end_right, var_used_right) = make_side(&second_last.2.right, &last.2.right);
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
    end: Config {
      state: last.1,
      left: end_left,
      head: last.2.head,
      right: end_right,
    },
  };
  vec![rule]
}

pub fn detect_rules<S: TapeSymbol>(
  step: u32,
  state: State,
  exptape: &ExpTape<S, u32>,
  signatures: &mut DefaultHashMap<Signature<S>, Vec<(u32, State, ExpTape<S, u32>)>>,
) -> Vec<Rule<S>> {
  let cur_sig_vec = &mut signatures[exptape.signature()];
  cur_sig_vec.push((step, state, exptape.clone()));
  if cur_sig_vec.len() > 1 {
    let rules = detect_rule(cur_sig_vec);
    if rules.len() > 0 {
      println!(
        "using steps: {:?} detected rule:\n{}\n",
        cur_sig_vec.iter().map(|(s, _, _)| s).collect_vec(),
        rules.first().unwrap()
      );
    }
    return rules;
  }
  return vec![];
}

pub fn simulate_detect_rules<S: TapeSymbol>(
  machine: &impl Turing<S>,
  num_steps: u32,
  rulebook: &Rulebook<S>,
  verbose: bool,
) -> (State, u32) {
  /*
  the plan to detect rules:
  store the signatures of everything seen so far
  if you see the same signature more than once, there is a possible rule
  */
  let mut exptape = ExpTape::new();
  let mut state = START;
  // let mut rulebook = Rulebook::new(machine.num_states());
  let mut signatures: DefaultHashMap<Signature<S>, Vec<(u32, State, ExpTape<S, u32>)>> =
    defaulthashmap!();
  for step in 1..num_steps + 1 {
    state = one_rule_step(machine, &mut exptape, state, rulebook, step, verbose).0;
    if state == HALT {
      return (HALT, step);
    }
    detect_rules(step, state, &exptape, &mut signatures);
  }

  return (state, num_steps);
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
            let end = Config {
              state: state_in,
              left: vec![],
              head: symbol_in,
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
              head: symbol_in,
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
  ) -> Option<(Self, Option<(Var, Self)>)> {
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
) -> Option<(SymbolVar, Option<(Var, SymbolVar)>)> {
  // returns the svar left on the tape and what to send the var in the affinevar to
  /*
  examples (avar match svar)
  5 match 6 returns 1
  5 match 4 returns -1
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
  if a == 0 {
    return Some((svar, None));
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
    svar,
    Some((
      avar,
      SymbolVar { n: integer_in_x, a: coeff_a_in_x, var: svar.var },
    )),
  ))
}

pub fn prove_rule<S: TapeSymbol>(
  machine: &impl Turing<S>,
  rule: Rule<S>,
  rulebook: &Rulebook<S>,
  prover_steps: u32,
  too_negative: i32,
  verbose: bool,
) -> Option<(Rule<S>, RuleProof)> {
  /* basic structure:
  1) set up tape with rule start
  2) simulate forward until rule end or step limit
  caveats:
    we have most of the simulation code written, but it will need to be generalized
    right now the tape freely adds symbols from the left and right implicit ends of the tape,
     but we don't want this behavior
  */
  if verbose {
    println!("working to prove rule: {}", &rule);
  }

  let Rule { start, end } = rule;
  let (mut state, mut proving_tape) = start.clone().to_tape_state();
  let (goal_state, goal_tape) = end.clone().to_tape_state();

  let mut neg_map: DefaultHashMap<Var, i32> = defaulthashmap! {0};

  for step in 1..prover_steps + 1 {
    let (new_state, hm) = one_rule_step(machine, &mut proving_tape, state, rulebook, step, verbose);
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
        println!("proving the rule failed due to negativity");
        return None;
      }
    }

    // check if we succeeded
    if state == goal_state && proving_tape == goal_tape {
      println!("proving the rule suceeded");
      return Some((
        package_rule(Rule { start, end }, &neg_map),
        DirectSimulation(step),
      ));
    }
  }
  println!("proving the rule failed");
  return None;
}

fn update_affine_var(
  AffineVar { n, a, var }: AffineVar,
  neg_map: &DefaultHashMap<Var, i32>,
) -> AffineVar {
  let amt_to_add: u32 = neg_map[var].abs().try_into().unwrap();
  AffineVar { n: n + amt_to_add, a, var }
}

fn update_config<S>(
  Config { state, left, head, right }: Config<S>,
  neg_map: &DefaultHashMap<Var, i32>,
) -> Config<S> {
  Config {
    state,
    left: left
      .into_iter()
      .map(|(s, avar)| (s, update_affine_var(avar, neg_map)))
      .collect(),
    head: head,
    right: right
      .into_iter()
      .map(|(s, avar)| (s, update_affine_var(avar, neg_map)))
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
  for step in 1..num_steps + 1 {
    state = one_rule_step(machine, &mut exptape, state, rulebook, step, verbose).0;
    if state == HALT {
      return (HALT, step);
    }
    let rules = detect_rules(step, state, &exptape, &mut signatures);
    for rule in rules {
      if let Some((final_rule, pf)) = prove_rule(machine, rule, rulebook, 20, -5, verbose) {
        println!("proved rule: {}\nvia proof{:?}", final_rule, pf);
        rulebook.add_rule(final_rule);
      }
    }
  }
  return (state, num_steps);
}

pub mod parse {

  use nom::{
    branch::alt,
    bytes::complete::{is_a, tag},
    character::complete::{char, one_of},
    combinator::{map, map_res, recognize},
    error::{FromExternalError, ParseError},
    multi::{many0, many1, separated_list0},
    sequence::{delimited, separated_pair, terminated, Tuple},
    IResult,
  };
  use std::num::ParseIntError;

  use crate::{
    simulate::ExpTape,
    turing::{Bit, State},
  };

  use super::{AffineVar, Config, Rule, Var};

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

  pub fn parse_count<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
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

  pub fn parse_count_tuple<
    'a,
    E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
  >(
    input: &'a str,
  ) -> IResult<&str, (Bit, AffineVar), E> {
    delimited(
      tag("("),
      separated_pair(parse_bit, tag(", "), parse_count),
      tag(")"),
    )(input)
  }

  pub fn parse_config_tape_side<
    'a,
    E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>,
  >(
    input: &'a str,
  ) -> IResult<&str, Vec<(Bit, AffineVar)>, E> {
    separated_list0(char(' '), parse_count_tuple)(input)
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
  ) -> IResult<&str, Config<Bit>, E> {
    let (input, (_, state_digit, _, left, _, head, _, mut right)) = (
      tag("phase: "),
      parse_u8,
      tag("  "),
      parse_config_tape_side,
      tag(" |>"),
      parse_bit,
      tag("<| "),
      parse_config_tape_side,
    )
      .parse(input)?;
    right.reverse();
    Ok((
      input,
      Config { state: State(state_digit), left, head, right },
    ))
  }

  pub fn parse_rule(input: &str) -> IResult<&str, Rule<Bit>> {
    let (input, (start, _, end)) = (parse_config, tag("\ninto:\n"), parse_config).parse(input)?;
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
        parse_count::<nom::error::Error<&str>>("3 + 5*x_0"),
        Ok(("", AffineVar { n: 3, a: 5, var: Var(0) }))
      );
      assert_eq!(
        parse_count::<nom::error::Error<&str>>("7 + 234*x_11"),
        Ok(("", AffineVar { n: 7, a: 234, var: Var(11) }))
      );
      assert_eq!(
        parse_count::<nom::error::Error<&str>>("7"),
        Ok(("", AffineVar { n: 7, a: 0, var: Var(0) }))
      );
    }

    #[test]
    fn test_parse_tuple() {
      assert_eq!(
        parse_count_tuple::<nom::error::Error<&str>>("(F, 1)"),
        Ok(("", (Bit(false), AffineVar::constant(1))))
      );
      assert_eq!(
        parse_count_tuple::<nom::error::Error<&str>>("(F, 0 + 1*x_0)"),
        Ok(("", (Bit(false), AffineVar { n: 0, a: 1, var: Var(0) })))
      );
      assert_eq!(
        parse_count_tuple::<nom::error::Error<&str>>("(T, 1 + 3*x_2)"),
        Ok(("", (Bit(true), AffineVar { n: 1, a: 3, var: Var(2) })))
      );
      assert!(parse_count_tuple::<nom::error::Error<&str>>("(T, 1 + 3*x_2").is_err())
    }

    #[test]
    fn test_parse_tape_side() {
      assert_eq!(
        parse_config_tape_side::<nom::error::Error<&str>>("(F, 1) (T, 1 + 1*x_0)"),
        Ok((
          "",
          vec![
            (Bit(false), AffineVar::constant(1)),
            (Bit(true), AffineVar { n: 1, a: 1, var: Var(0) })
          ]
        ))
      );
      assert_eq!(
        parse_config_tape_side::<nom::error::Error<&str>>("(F, 0 + 1*x_0) (T, 1)"),
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
      let ans: Result<(&str, Config<Bit>), nom::error::VerboseError<&str>> =
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
      assert_eq!(parse_rule(rule_str), Ok(("", Rule { start, end })));
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
  use nom::Finish;

  use crate::{
    rules::parse::{parse_avar, parse_avar_gen, parse_rule, parse_tape},
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
      end: Config {
        state: State(1),
        left: vec![(Bit(false), AffineVar { n: 0, a: 1, var: Var(0) })],
        head: Bit(true),
        right: vec![],
      },
    };
    let rule2 = Rule {
      start: Config {
        state: State(3),
        left: vec![(Bit(true), AffineVar { n: 0, a: 1, var: Var(0) })],
        head: Bit(true),
        right: vec![],
      },
      end: Config {
        state: State(3),
        left: vec![],
        head: Bit(true),
        right: vec![(Bit(true), AffineVar { n: 0, a: 1, var: Var(0) })],
      },
    };
    assert_eq!(detected_rules, vec![rule1, rule2]);
  }

  #[test]
  fn test_match_var_num() {
    let (_leftover, var) = parse_avar_gen::<nom::error::Error<&str>>(&"3 + 2*x_0").unwrap();
    assert_eq!(match_var_num(var, 3, false), None);
    assert_eq!(match_var_num(var, 5, false), Some((0, Some((Var(0), 1)))));
    assert_eq!(match_var_num(var, 6, false), Some((1, Some((Var(0), 1)))));
    let (_leftover, var) = parse_avar_gen::<nom::error::Error<&str>>(&"3 + 0*x_0").unwrap();
    assert_eq!(match_var_num(var, 3, false), Some((0, None)));
    assert_eq!(match_var_num(var, 5, false), Some((2, None)));
  }

  #[test]
  fn test_match_rule_tape() {
    let rule_str = "phase: 3  (F, 1) (T, 1 + 1*x_0) |>T<| 
into:
phase: 1  (T, 1) |>F<| (F, 0 + 1*x_0) (T, 1)";
    let (_leftover, rule) = parse_rule(rule_str).unwrap();
    let tape_str = "(T, 1) |>T<| (T, 7)";
    let (_leftover, mut tape) = parse_tape(tape_str).unwrap();
    let tape_copy = tape.clone();
    println!("app1");
    assert_eq!(apply_rule_hm(&mut tape, State(3), &rule, true), None);
    assert_eq!(tape, tape_copy);
    //now we apply the rule to a tape that works
    let tape_str = "(T, 2) |>T<| (T, 7)";
    let output_str = "(T, 1) |>F<| (F, 1) (T, 8)";
    let (_leftover, mut tape) = parse_tape(tape_str).unwrap();
    let (_leftover, output_tape) = parse_tape(output_str).unwrap();
    println!("app2");
    assert_eq!(apply_rule(&mut tape, State(3), &rule, true), Some(State(1)));
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
    assert_eq!(apply_rule(&mut tape, State(3), &rule, true), Some(State(1)));
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
    assert_eq!(apply_rule(&mut tape, State(3), &rule, true), Some(State(1)));
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
    let new_rule_state = one_rule_step(machine, rule_tape, rule_state, rulebook, step, verbose).0;
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
      Some((SymbolVar::constant(1), None))
    );
    assert_eq!(
      match_avar_svar(a5, SymbolVar::constant(4)),
      Some((SymbolVar::constant(-1), None))
    );
    assert_eq!(
      match_avar_svar(a5, SymbolVar { n: 0, a: 1, var: Var(0) }),
      Some((SymbolVar { n: -5, a: 1, var: Var(0) }, None))
    );

    let x = AffineVar { n: 0, a: 1, var: Var(0) };
    let stuff = SymbolVar { n: 3, a: 2, var: Var(1) };
    assert_eq!(
      match_avar_svar(x, stuff),
      Some((SymbolVar::constant(0), Some((Var(0), stuff))))
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
        SymbolVar::constant(0),
        Some((Var(0), SymbolVar::constant(3)))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x, SymbolVar::constant(7)),
      Some((
        SymbolVar::constant(1),
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
        SymbolVar { n: 0, a: 1, var: Var(0) },
        Some((Var(0), SymbolVar { n: 0, a: 1, var: Var(0) }))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x, SymbolVar { n: -1, a: 2, var: Var(0) }),
      Some((
        SymbolVar { n: 1, a: 0, var: Var(0) },
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
        SymbolVar::constant(1),
        Some((Var(0), SymbolVar::constant(1)))
      ))
    );
    assert_eq!(
      match_avar_svar(two_x_p3, SymbolVar::constant(7)),
      Some((
        SymbolVar::constant(0),
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
        SymbolVar::constant(1),
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
        SymbolVar { n: 1, a: 1, var: Var(0) },
        Some((Var(0), SymbolVar { n: -2, a: 1, var: Var(0) }))
      ))
    );
  }
}
