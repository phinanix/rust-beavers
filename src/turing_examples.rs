use std::collections::HashMap;

use crate::{run_machine, turing::SmallBinMachine};

pub fn decrease_rules_make_worse() -> Vec<&'static str> {
  //16 machines that _stop_ being proven when you enable rules that decrease a var by >1
  /*
  machine 0:
  straightforward bouncer that goes right with BBC and left with B, but has a
  nontrivial turnaround at the right side
  we prove the left rule as a chain rule
  then prove the right rule on step 13
  but then on step 25 we make the following bad guess:
    phase: C  (F, 1) (T, 1 + 1*x_0) |>T<| (F, 3 + 1*x_0)
    into:
    phase: C  (T, 4 + 1*x_0) |>T<| (F, 1 + 1*x_0)
  which is true, but chaining it forces x_0 to be even which is not a necessary restriction
  and for some reason we never guess the smarter version
  conclusion: better guessing would probably help

  machine 11 (chosen randomly):
  bouncer goes right with C left with D, both proven as chain rules
  same deal, we make and prove the bad rule on step 19:
    phase: C  (F, 3 + 1*x_0) |>T<| (T, 1 + 1*x_0) (F, 1)
    into:
    phase: C  (F, 1 + 1*x_0) |>T<| (T, 4 + 1*x_0)
  v similar to above, the bad guess is due to:
    detecting rule from
    (F, 3) |>T<| (T, 3) (F, 1)
    to
    (F, 1) |>T<| (T, 6)
  which like, better rule guessing would fix, as would readshifts-when-proving
  but why does this machine work without decrease of more than 1 chaining?
  well we still make all the dumb guesses, but now we can't chain them, so we keep simulating
  until we get to step 25:
    detecting rule from
    (F, 2) |>F<| (T, 5) (F, 1)
    to
    |>F<| (T, 8)
    using steps: [16, 25] detected rule:
    phase: D  (F, 2) |>F<| (T, 0 + 1*x_0) (F, 1)
    into:
    phase: D   |>F<| (T, 3 + 1*x_0)
  which is a non-dumb rule guess that is provable and chainable and then we prove the machine
     */
  vec![
    "1RB1LA_1RC1LB_1RD0RB_0LA1RH",
    "1RB0RC_1RC1RH_0LD1LD_1RA1LD",
    "1RB0LC_1RC1RH_0LD1RD_1RA1LD",
    "1RB0LB_1RC1RD_0LD1RH_1RA1LD",
    "1RB1LD_1RC1LB_0LB1RA_1RH1RC",
    "1RB1LD_1RC1LB_0LB1RA_1RH0RB",
    "1RB1RA_1LC1RH_0RA1RD_1LB1LD",
    "1RB1RH_1LC1LB_1RD1RC_0LB0RC",
    "1RB1RH_1LC1LB_1LD1RC_0RC1RB",
    "1RB1RH_1LC1LB_1LD1RC_0RC1LB",
    "1RB1RA_1LC1LB_1LD1RB_0RA1RH",
    "1RB1RH_0RC1RD_1LB1RC_1LC1LD",
    "1RB1RH_0RC1LD_1LB1RC_1LC1LD",
    "1RB0RD_0LC1RH_1RD1LC_1RA1LD",
    "1RB1LA_0LC0RA_1RD1LC_1RH1RA",
    "1RB0RD_0LC1RH_1LD1LC_1RA1LD",
  ]
}

pub fn undecided_size_3() -> Vec<&'static str> {
  // 39 strings
  vec![
    "1RB1RH_1RC0LC_1LB0RB",
    "1RB1RH_1RC1LB_0LB0RC",
    "1RB1LA_1RC1RB_1LA1RH",
    "1RB0RB_1LC1RH_0LA1RC",
    "1RB1RA_1LC1RH_1RA1LC",
    "1RB1RA_1LC1RH_0RA1LC",
    "1RB1RH_1LC1RB_0RB0LC",
    "1RB1RH_1LC1RB_0RA0LC",
    "1RB1RH_1LC1RA_0RA0LC",
    "1RB1RH_1LC0RB_0LC1RB",
    "1RB1RH_1LC0RC_1RB0LB",
    "1RB1RH_1LC0RA_1RB0LB",
    "1RB1RH_1LC0RA_0RB0LB",
    "1RB1RC_1LC1RH_0RA0LB",
    "1RB1LA_1LC0LC_1RH1RA",
    "1RB1LC_1LC1RB_1RH1LA",
    "1RB0LB_1LC1RB_1RH1LA",
    "1RB1RH_1LC0RB_1LB1LA",
    "1RB1RC_0RC1RH_1LC0LA",
    "1RB0RC_0RC1RH_1LC0LA",
    "1RB1RH_0RC0LB_1LB1RC",
    "1RB1RH_0RC1LB_1LA0LA",
    "1RB1RH_0LC0RB_1RB1LC",
    "1RB1RH_0LC1RB_1LA1LC",
    // T bouncer A one way, C the other (??)
    "1RB1RA_0LC1RH_0RA1LC",
    "1RB1RH_0LC0RA_1LA1LB",
    "1RB1RH_0LC0RB_0RA1LB",
    // TF both ways bouncer
    "1RB1RH_0LC0RA_0RA1LB",
    // TF / TT bouncer
    "1RB0LC_0LC1RA_1RH1LA",
    // TF / TT bouncer
    "1RB0LC_1LB1RA_1RH1LA",
    // F/T right counter
    "1RB1RH_0LB1RC_1LB0RC",
    // T bouncer, ABC 1 way, and B the other way
    "1RB0RC_1LA1RB_1RH1LB",
    // TF both ways bouncer
    "1RB0LC_1LA0RA_1LA1RH",
    // TF both ways bouncer
    "1RB0LB_1LA0RC_1RB1RH",
    // T bouncer, BC 1 way, and A the other way
    "1RB1LA_1LA1RC_1RH1RB",
    // T bouncer, ABC 1 way, and A the other way
    "1RB1LA_1LA0LC_1RH1RA",
    // FF / TF left counter
    "1RB1LC_0LA0RB_1LA1RH",
    // TF both ways bouncer
    "1RB0LC_0LA0RA_1LA1RH",
    // T bouncer, ABC 1 way, and A the other way
    "1RB1LA_0LA0LC_1RH1RA",
  ]
}
// running machine: 1RB1LA_0LA0LC_1RH1RA

/* size 4 overall total
 19 readshifts
   2(?) lr readshift (may not have caught all of these, some might have been put as failure to guess)
   17 readshift
 24 bouncer
   17 size2
   2(?) size2 2pass (not confident I caught all these)
   5 size3
 5 counters
   2 size1
   3 size2
 12 failure to guess
   7 chain rule
   5 normal

*/
pub fn undecided_size_4_random() -> Vec<&'static str> {
  /*
   30 random machines chosen from the set of 20747 generated on 2 May 23
   with
   let num_undecided_to_display = 30;
   let seed = 12345678901234;
  */
  // wow, of these 5, only 1 seems like it should actually not be provable by my program!
  /*
  0 - readshifts
  1 - readshifts
  2 - readshifts
  3 - TT / TF so needs size 2 macro
  4 - readshifts
  5 - FF / TF counter
  6 - readshifts
  7 - TF / TF
  8 - TT / TF
  9 - readshifts
  counts:
  6 readshifts
  3 size2 bouncers
  1 size2 counter

  10 - TF / TF bouncer
  11 - BCD one way, BD other way bouncer, we guess one rule but not the other
  12 - ABC one way, CD other way bouncer, we guess one rule but not the other
  13 - failure to guess rule (?) (B going R, BBCD going L)
  14 - readshifts
  15 - readshifts
  16 - TFF / FTT bouncer
  17 - F/T counter (2 states lol)
  18 - failure to guess rule (?) (D going R, AC going L)
  19 - readshifts
  counts:
  3 readshifts
  4 (?) failure to guess rule
    2 normal
    2 chain rule
  1 size2 bouncer
  1 size3 bouncer
  1 size1 counter (that is also a closed state graph but eh)

  total:
  9 readshifts
  5 bouncers of larger size
  4 (?) failure to guess rule
  2 counters

  20 - readshifts
  21 - TF / TF bouncer
  22 - TTF / TTF bouncer
  23 - failure to guess rule (?) (A going L, ABCD going R)
  24 - TTF / TTT bouncer
  25 - TF / TF bouncer
  26 - TT / TF bouncer
  27 - TF / TF bouncer
  28 - TF / TF bouncer
  29 - readshifts
  counts:
  5 size2 bouncer
  2 size3 bouncer
  2 readshifts
  1 (?) failure to guess
    1 chainrule

  total:
  12 bouncers of larger size
    9 size2
    3 size3
  11 readshifts
    11 readshifts
  5 failure to guess
    3 chainrule
    2 normal
  2 counters
    1 size1
    1 size2
   */

  vec![
    "1RB1LB_0LC0LD_1RD1LC_1RH1RA",
    "1RB1RH_1LC0RB_0RD1RB_0RD1LB",
    "1RB1RC_1RC1RH_1LD1RC_1LA0LA",
    "1RB1LD_0RC1RH_1LD0LD_1RA0LA",
    "1RB0RB_0RC1LB_0LD0LA_1LB1RH",
    "1RB0RB_1LC1RD_0RA0LC_1RB1RH",
    "1RB0RC_1LA1RB_1LB1LD_1LA1RH",
    "1RB1RD_1LC1RH_0RA0LB_0LD1RC",
    "1RB0LC_1LA1RA_1LA0LD_1RH1RB",
    "1RB1LD_1LC0RB_0RA1RB_1LC1RH",
    "1RB0LB_1LC0RA_0LB0LD_1LA1RH",
    "1RB1LC_1LC1RD_1RH0LD_1RA1RB",
    "1RB0RB_1LC1RH_0LA1RD_0RB1RC",
    "1RB1RD_1LC1RB_1RH1LD_1RB0LB",
    "1RB1RA_1LC1LB_0RD0RB_1RH0RA",
    "1RB0RB_0LC1LD_1RH1RD_1LA1RD",
    "1RB1LC_1LA0RD_0LB1RH_1RB0RD",
    "1RB1RH_0LC0RA_0RD0LC_1LC1RD",
    "1RB1LC_0LC1LD_1RH1LA_1RB1RD",
    "1RB1LD_1LC1RB_0RB0RD_1RH1LB",
    "1RB0RB_1LC0RB_0RD1RA_1RH1LB",
    "1RB0RC_1LA1RH_1RA0LD_1LC0LD",
    "1RB1LD_1RC1RH_0LA0RC_0LA1LD",
    "1RB1LA_1LA0RC_1RD0LD_1RA1RH",
    "1RB0RD_0RC1RH_0LD1RA_1LD0LA",
    "1RB0LC_1LA0RD_1LA1RH_1RB0LB",
    "1RB1RH_0LC1RA_1LB0LD_1LA1LC",
    "1RB0RC_0LC0RA_1LD1LB_1RB1RH",
    "1RB1LD_0RC1RH_1RD0RD_0LA1RB",
    "1RB1RA_0LC0LD_1RB1LC_1RH1RA",
  ]
}

pub fn undecided_size_4_random_100() -> Vec<&'static str> {
  /*
  100 random machines chosen from the same set of 20747 for additional categorization
    let num_undecided_to_display = 100;
  let seed = 123456789012345; */
  /*
    0 - LR readshift
    1 - TFF / TFF bouncer
    2 - FF / FT counter
    3 - readshift
    4 - TF / TF bouncer
    5 - failure to guess even though other way is chain rule
    6 - TF / TF bouncer
    7 - TT / FT bouncer (2-pass)
    8 - TT / FT bouncer (2-pass)
    9 - CD right, ABC left failure to guess
    counts:
    2 readshift
      1 lr readshift
      1 readshift
    5 bouncer
      2 size2
      2 size2 2pass
      1 size3
    1 counter
      1 size2
    2 failure to guess
      1 chain rule
      1 normal

   10 - TFF / TFF bouncer
   11 - TF / TF bouncer
   12 - F / T counter
   13 - readshift
   14 - TT / TF bouncer
   15 - failure to guess even though other way is chain rule
   16 - readshift
   17 - has a leftgoing rule and a rightgoing rule, but doesn't prove a "full" rule (oh b/c readshift)
   18 - readshfit
   19 - AC left, ABD right, failure to guess
    counts:
    4 readshift
      1 lr readshift
      3 readshift
    3 bouncer
      2 size2
      1 size3
    1 counter
      1 size1
    2 failure to guess
      1 chain rule
      1 normal

   20 - readshift
   21 - readshift
   22 - failure to guess even though other way is chain rule
   23 - failure to guess even though other way is chain rule
   24 - TF / TF bouncer
   25 - FF / FT counter
   26 - TF / TF bouncer
   27 - TT / TF bouncer
   28 - ABC right, CD left, failure to guess
   29 - TT / TF bouncer
    counts:
    2 readshift
      2 readshift
    4 bouncer
      4 size2
    1 counter
      1 size2
    3 failure to guess
      2 chain rule
      1 normal

    total counts:
    8 readshift
      2 lr readshift
      6 readshift
    12 bouncer
      8 size2
      2 size2 2pass
      2 size3
    3 counter
      1 size1
      2 size2
    7 failure to guess
      4 chain rule
      3 normal
   classifying took 18.5m so that's 37s / machine.

  */
  vec![
    "1RB0RC_1LA0LD_0RB1LB_1RH1RA",
    "1RB0LC_0RC0RA_1LD0RA_0LA1RH",
    "1RB1LC_1LC1RA_0RD0LC_1RB1RH",
    "1RB1LA_1LC0RA_1LC1LD_1RA1RH",
    "1RB1RC_1LA0RA_0RA0LD_1RH1LB",
    "1RB1RA_1LC0RA_1RH1LD_0RA1LC",
    "1RB0LB_0RC0RA_0LD1RH_1LA1RD",
    "1RB1RH_1LC1RD_1LD1LD_1RB0LC",
    "1RB1LC_1RC1RH_1LA0RD_0LA1LD",
    "1RB0RB_1LC1RH_0LA1RD_1RA1RC",
    "1RB0LC_0RC0LD_1LD0RA_0LA1RH",
    "1RB1RD_0LC1LC_1RD1LB_0RA1RH",
    "1RB1RH_1RC0RB_0RD0LC_1LC1RD",
    "1RB1LC_1LC1RB_1RH0LD_0RA1RB",
    "1RB1RH_1LC0RD_1RC1LB_1RC1RB",
    "1RB1RH_0LC1RB_0RA1LD_1LB1LC",
    "1RB1LA_1RC0LD_1LD1RH_1RB1RA",
    "1RB1RD_0RC0RA_0LD0LA_1LC1RH",
    "1RB0RB_1LC1RB_0RD0LB_1RH1RA",
    "1RB1LC_1LA0LD_1LB1LA_1RH1RA",
    "1RB1RH_0LC0LD_1RB1LC_1RC1RC",
    "1RB1LB_1LC0RD_1LC1LA_1RH1RA",
    "1RB1RH_1LC0RD_1LC1RD_0RC0RB",
    "1RB1RA_1LC1LC_1LD1LB_0RA1RH",
    "1RB1RH_0LC0RA_1LD1LB_0RB1LA",
    "1RB1RH_0RC0LB_1RD1LB_1LD1RC",
    "1RB1RC_0LA1RH_1RD0LD_1LC0RC",
    "1RB1RH_1RC0LD_1LB0RD_0LA1LB",
    "1RB0RB_1LA1LC_1RA1LD_1RH1LC",
    "1RB1LB_1RC0RD_0LA1RB_1RH1LC",
    "1RB1RA_0LB1LC_0RA1RD_1RH1LB",
    "1RB1RH_0LC0LD_1LA1LC_1LA1RA",
    "1RB1LA_1LC0LD_1RH1LD_1RD1RA",
    "1RB1LD_0LC0RC_0LD0RC_1LA1RH",
    "1RB1LC_1LA1RH_0RC1LD_1RC0LD",
    "1RB1RH_1RC1RD_0RD1LC_1LD0LB",
    "1RB1LC_0LA1RD_1LA1LC_1RH0RB",
    "1RB1RH_1LC0LD_1RB1LC_1RC1RA",
    "1RB0RB_1LA1LC_1LA1RD_1RH1RB",
    "1RB1LB_0LC1RH_1LD0RD_1RC0LC",
    "1RB1RH_1RC1LD_0LB1RD_0RC0LD",
    "1RB1LA_1LA0RC_0LD1RC_1RH1LB",
    "1RB0LD_0LC1RA_1RH1RD_0LD1LA",
    "1RB1RH_1LC1LC_1RD0LB_0LC0RC",
    "1RB1RC_0LB1RC_0RD1RH_1LB0RC",
    "1RB1RH_0RC0LC_0RD1RD_1LB1RD",
    "1RB0LB_1LA0RC_1RD1LA_1RH0RA",
    "1RB1LC_0LC1RA_1RH1LD_1RB0LC",
    "1RB1RC_0LC1RD_1LA1LC_1RH0RB",
    "1RB1LA_1LA0RC_0LD0LD_1RA1RH",
    "1RB0LB_1LA0RC_1RD0LC_1RH0RA",
    "1RB1RH_0RC1LB_1LD0LD_1RB0LB",
    "1RB0LD_1LC0RA_0RB1LD_1LA1RH",
    "1RB0LC_0LA0RA_1RD1LA_0RB1RH",
    "1RB0RB_0RC0LC_1LB0RD_1RC1RH",
    "1RB1RB_1LC0LD_1RA1LC_1RH0RB",
    "1RB1RH_1RC0LA_1LD0RB_1LB0LC",
    "1RB1LD_1LC0RD_1RH1RA_1RA1LA",
    "1RB1LA_1LC0LC_1RH1RD_1RB0LA",
    "1RB1RH_1LC0RB_1RD1LA_1LC1LD",
    "1RB1RD_1RC0LA_0LB1RC_1LB1RH",
    "1RB1LA_1LC0RD_0RB0LB_1RB1RH",
    "1RB1RB_0LC1RA_0LD1LC_1LA1RH",
    "1RB0LC_1LC1RH_0RD0LB_0LB1RC",
    "1RB1RH_0RC1LD_1LA0LA_0RC1LD",
    "1RB0LD_0LC0RC_1RB0LD_1LC1RH",
    "1RB0LD_1RC1LB_1LB0LD_1RH1RB",
    "1RB1LA_0LC0RD_1LD1LB_1RB1RH",
    "1RB1LD_1RC1RH_0LA0RC_1LD0LA",
    "1RB1RH_1LC0LD_1LB1RD_1RB1RC",
    "1RB1RD_1LC0RC_1RD1LB_1RH1RA",
    "1RB1RD_0LC0RB_1RB1LD_1LC1RH",
    "1RB0RC_1LA1RB_1RH1LD_1LA0RA",
    "1RB1LC_0LA1RC_0RB0LD_0RB1RH",
    "1RB1RH_0LC1RA_1LC0LD_1LA0RB",
    "1RB0RC_1LA0RA_1RH1LD_0LB0RA",
    "1RB0LA_1LC1RB_1RB0RD_1RH1LB",
    "1RB1RH_1LC0RD_1RB1LB_0LB1RD",
    "1RB0RB_1LC1RD_1RC0LB_0RA1RH",
    "1RB1RH_1RC1LB_1LB1RD_0LB1RC",
    "1RB0RB_0RC1LD_0RD1RH_1LA1RD",
    "1RB1RH_1LC0LC_0RA1RD_1RB1LD",
    "1RB1RD_1LC0RA_0LD0LB_1RA1RH",
    "1RB1LC_1LC0RD_1RA1LA_1RH1RA",
    "1RB1LB_1RC0LA_1LC0LD_1RH1RA",
    "1RB1RC_1LC1LD_0RA1RB_1RH0LB",
    "1RB1RD_1LC1RB_1RH1LA_1LC0LB",
    "1RB0LD_1LC0RA_1LD0LB_1LA1RH",
    "1RB1RH_0RC0RB_1LD1LA_0LB0LB",
    "1RB1LD_1RC1RH_0LA0RC_1LD1LC",
    "1RB0LB_1LA1RC_1RD1RH_0RA0RC",
    "1RB1RH_1LC0RC_1RD1LB_1RA1RD",
    "1RB1RD_1RC1RH_0RD0RD_1LD0LA",
    "1RB1LB_0LC1RH_1LD1RC_0RC0LD",
    "1RB1RH_1RC0LA_1LD0RD_0RB1LD",
    "1RB0LA_0LC0RB_0RA1LD_1LB1RH",
    "1RB0LC_1LC1RD_0RA0LC_1RA1RH",
    "1RB1RB_0LC1RA_0RA0RD_1LB1RH",
    "1RB0LD_1RC1RA_1LD1RH_1RA1LA",
    "1RB1RD_1LC1RH_0RD0LC_0LB1RC",
  ]
}

pub fn decided_by_chain_update_31may() -> Vec<&'static str> {
  vec![
    "1RB1LD_1LB0LC_0LD1RH_1RD0RA",
    "1RB1RH_1LB0LC_1RC0RD_0LA1LC",
    "1RB1RC_1LB1LA_0RD0RC_0LB1RH",
    "1RB1LC_1LB1LA_1RD1RB_1RH0RC",
    "1RB1LC_1LB1LA_1RD0RB_1RH0RC",
    "1RB1LC_1LB1LA_1RD1RB_1RH0RA",
  ]
}

pub fn scan_3_dregs() {
  for m_str in undecided_size_3() {
    let machine = SmallBinMachine::from_compact_format(m_str);
    run_machine(&machine);
  }
}

pub fn scan_3_size_2() {
  let two_state_no_halt_from_scan_3 = vec![
    /*
    A FF FF< (TF, n) FF
    A FF< (TF, n+2)
     */
    "1RB0LB_1LA0RA",
    /*
    phase: B  (F, 1) (T, 1 + 1*x_0) |>F<| (F, 1)
    into:
    phase: B  (T, 3 + 1*x_0) |>F<|
     */
    "1RB1LA_1LA1RB",
    /*
    phase: A  (F, 1) |>F<| (T, 1 + 1*x_0) (F, 1)
    into:
    phase: A   |>F<| (T, 2 + 1*x_0) (F, 1)
     */
    "1RB1LA_0LA1RB",
    // binary counter, count grows leftwards
    "1RB1LA_0LA0RB",
  ];
  for m_str in two_state_no_halt_from_scan_3 {
    let machine = SmallBinMachine::from_compact_format(m_str);
    run_machine(&machine);
  }
}

/*
notes on the machines:
counter_like is not quite an actual counter I think but the proof is very similar, it is
in the haskell repo (todo: figure out how to analogize it to a counter)
answer: it's a fibonacci counter, with the invariant that there is no FTF anywhere

tailEatingDragonFast satisfies
A (T, x) >T<
A (T, 3x) >T<
(eg 12, 57, 285)
via subrules such as
A T >T< F
A >T< F T
giving
A (T, x) >T< F
A >T< F (T, x)
as well as
A >T< (F, 1) (T, 3)
D (T, 3) (F, 1) >T<
and the chain rule
D >T< (T, x)
D (T, x) >T<
leading to an overall behavior (57, 95) of *
A (F, 3)        (T, x) >T<
A (T, 3) (F, 1) (T, x-1) >T<
and (95, 130)
A FF (T, x) (F, 1) (T, y) >T<
A (T, x+3) (F, 1) (T, y-1) >T<
which chains to
A (F, 2y) (T, x) (F, 1) (T, y) >T<
A (T, x+3y) (F, 1) >T<
which along with * gives
A (F, ??) (T, x)
A (T, 3) (F, 1) (T, x-1)
A (T, 3x) (F, 1) >T<
which is almost right if you fiddle a little

my rule prover proves:

phase: C  (T, 1 + x) |>F<| (T, x)
into:
phase: C  (T, 1) |>F<| (T, 2*x)

phase: A  (T, 1 + x) |>T<| (F, 1) (T, x)
into:
phase: A  (T, 1) |>T<| (F, 1) (T, 2*x)

phase: D  (T, 1 + x) (F, 1) |>F<| (T, x)
into:
phase: D  (T, 1) (F, 1) |>F<| (T, 2*x)
 */
const MACHINES: [(&str, &str); 9] = [
  ("bb2", "1RB1LB_1LA1RH"),
  ("bb3", "1RB1RH_0RC1RB_1LC1LA"),
  // ("bb4", ""),
  ("binary_counter", "0LB0RA_1LC1LH_1RA1LC"),
  ("checkerboard_sweeper", "1RB0LC_0LC1RA_1LH1LA"),
  ("sweeper", "1RB1LH_0LC0RB_1LC1LA"),
  ("counter_like", "1RB0LC_0LA0RB_1RA1RD_1LA1RH"),
  ("tailEatingDragonFast", "1RB0RD_1RC1RH_0LA1RA_1LC1RD"),
  ("tailEatingDragonSlow", "1RB1LA_1RC0RD_1LA1RH_0LA1RD"),
  ("ternaryCounter", "1RB0LC_1LA1RA_0RA0LD_1RH1LC"),
];

pub fn get_machine(name: &str) -> SmallBinMachine {
  let machine_map = HashMap::from(MACHINES);
  SmallBinMachine::from_compact_format(
    machine_map
      .get(name)
      .expect(&format!("{} wasn't a valid machine name", name)),
  )
}

pub fn all_machine_examples() -> Vec<(&'static str, SmallBinMachine)> {
  let mut out = vec![];
  for (name, machine_str) in MACHINES {
    out.push((name, SmallBinMachine::from_compact_format(machine_str)));
  }
  out
}
