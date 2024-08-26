
/*
2 may 23 rule step to machine counts
7820 @ 42-1000
7819 @ 38-41
7818 @ 35-37
7817 @ 34
7816 @ 31-33
7814 @ 30
7810 @ 29
7807 @ 28
7798 @ 27
7789 @ 26
7772 @ 25
7725 @ 24
so the record holding machines take
42
38
35
34
2 @ 31
4 @ 30
3 @ 29
9 @ 28
9 @ 27
27 @ 26
47 @ 25
 */

24 July 2024
Testing BBB size 4
total machines: 2_943_669
halted: 183_983
undecided @ LR   750: 150_167  diff
          @ LR  1500: 149_912  255
          @ LR  3000: 149_822   90
          @ LR  6000: 149_778   44
          @ LR 12000: 149_758   20
          @ LR 24000: 149_742   16

          @ LR   384_000: 149_723 19
          @ LR 1_000_000: 149_720 3

(note rerunning @1M takes ~15m)

undecided @ LR   750: 150_167  diff ratio
          @ LR  1061: 149_988  179  
          @ LR  1500: 149_912   76  2.36
          @ LR  2121: 149_848   64  1.19
          @ LR  3000: 149_822   26  2.46
          @ LR  4243: 149_798   24  1.08
          @ LR  6000: 149_778   20  1.20
          @ LR  8485: 149_765   13  1.54
          @ LR 12000: 149_758    7  1.86
          @ LR 16971: 149_751    7  1
          @ LR 24000: 149_742    9  .78


qh first results: 
[src/beep.rs:359:5] machines.len() = 2943669
halted: 183983 quasihalted (cycled): 192528 quashalted (lr): 762015
non-qh (cycled): 151072 non-qh (lr): 1504159 inconclusive: 149912

[src/main.rs:141:3] machines.len() = 2943669
halted: 183983 cycled: 343600 lr: 2266174 inconclusive: 149912

halts match

cycs match
qh cyc + nqh cyc = 192528 + 151072 = 343600
cyc = 343600

lrs 
qh lr + nqh lr = 762015 + 1504159 = 2266174
lr = 2266174

inconclusives match

size4_qh_holdouts_24_july_24 is all machines that don't qh or nqh within 1M steps

30 July 24
random.org machines from 672 size 3
bouncer
counter
bouncer
bouncer
"cubic bouncer" / double bouncer

bouncer
bouncer
bouncer
bouncer
bouncer

8 bouncer 1 counter 1 cubic bouncer

goals: 
✓ run from list of saved machines
✓ look at some random machines from list of size 3 and size 4
✓ write "spec" / alg for bouncer decider
✓ implement bouncer decider

2 Aug 24 
new goals: 
✓ classify 10 holdouts from undecided size 4
- run brady bouncer alg on both size 4 domains
- classify 10-20 holdouts from quasihalt holdouts
- make bouncer alg detect quasi-halting
- pick what upgrades (if any) to make to bouncer alg 

first bug: 185
second: 
2068
running records of machine: 1RB0LD_1RC1RH_1LD0RD_1RA0LA
thread 'main' panicked at src/brady.rs:322:27:
range end index 9223372036854775838 out of range for slice of length 29

fixed bugs!
analyzed 29373 machines. bouncers: 20092 undecided: 9281

[src/main.rs:594:3] num_lr_steps = 1000
[src/main.rs:594:3] num_rule_steps = 200
tnf machines 1000000
tnf machines 2000000
halted: 183983 quasihalted (cycled): 192528 quashalted (lr): 762000
non-qh (cycled): 151072 non-qh (lr): 1504070 inconclusive: 150016
there were 150016 undecided machines
analyzed 150016 machines. bouncers: 87889 undecided: 62127

2 Aug 24 diff size
(this one is a mistake)
Language                     files          blank        comment           code
-------------------------------------------------------------------------------
Rust                            12            741           1276           6789
Rust                            12            805           1463           7310
                                 0             64            187            521

(this one is correct)
Rust                            12            746           1298           6812
Rust                            12            805           1463           7310
                                 0             59            165            498

total
 63,185 additions and 201 deletions 
holdouts file
 62,127 additions, 0 deletions
not holdouts file
 +1,059 - 201

https://github.com/phinanix/rust-beavers/compare/bb77c..6797c

adding limited support for bouncers growing on the left and not the right: 
analyzed 150016 machines. bouncers: 96514 undecided: 53502
proved 8625 machines, an additional 5.7%. 
estimated total grow_left bouncers: 22366
estimated remaining grow_left bouncers: 13741
est. 39% of grow left bouncers proven
around 1379 machines had no largest turnaround; the first one of this type I examined was a translated bouncer
(2.5%)
with shadow that grows to the left 
5 more: 
1RB1RB_1RC0RA_1LD0LC_1LA1LC
leftmoving translated bouncer with shadow two_stage
1RB0LC_1LC1LD_1LA1LC_0RA1RD
leftmoving translated bouncer, no shadow, but there is some stuff left on the tape from the beginning
1RB1LA_0LA0LC_1RD1LC_1RB1RD
"tail eating dragon", ie cubic bouncer that grows every step but has two inductions needed to prove 
1RB1LA_1RC1LB_0RD1RC_0LD0LA
leftmoving translated bouncer without shadow
1RB0LD_0RC1RB_0LD0LD_1LA1LD
leftmoving translated bouncer without shadow
1 shadow 3 no_shadow 1 tail_eating_dragon_fast



analyzed 29373 machines. bouncers: 22803 undecided: 6570
9281 -> 6570 = 2711 
reduced undecided machines by 29% 
there were an additional 13% bouncers who were grow_left
202 (3%) of machines had no biggest turnaround
5 of them were: 
1RB0LC_0LA1RD_1LA1LB_0RA1RH
leftmoving translated bouncer (no shadow)
1RB0LC_0LA0RA_0LD1RH_1LA1LC
same as prev (category and behavior)
1RB0LC_0LA1RB_1LD1LC_1LA1RH 
same as prev (category)
1RB1RH_0LC0LB_1RC0LD_1LB0RA
same as prev (category)
1RB0LD_1LC0RA_1RH1LA_1LA1LD
leftmoving translated bouncer with shadow
(all 5 were this, with or without shadow) 
4 no shadow 1 shadow

22 Aug 24
added additional support for bouncers that grow left

halted: 183983 quasihalted (cycled): 192528 quashalted (lr): 762000
non-qh (cycled): 151072 non-qh (lr): 1504070 inconclusive: 150016
there were 150016 undecided machines
analyzed 150016 machines. bouncers: 98118 undecided: 51898

I am confused though, as these numbers seem small to me 
we proved 98118 bouncers. previously we proved 87889 bouncers. 
so that's an additional 10229 bouncers. probably we just got 
somewhat unlucky here? I will have to do the stats it seems. 
As it is, the full bouncers project would reduce us from 
149720 machines to 51602, which is 2.9x, which isn't quite
as much as we hoped but it's overall not bad. 

the main stat I want when all this is done is % of that 51.6k 
that is a counter, which I'll want to aggregate some previous 
results for perhaps. 

I still have to produce the actual holdouts file, but currently 
the confirmed-proven-bouncers count is 99296

23 Aug 24
late yesterday I found a correctness bug: in steps 2 and 4 
(eg Z < Z1 -> < Z1 Z2) the start and end states need to match 
for the rule to apply arbitrarily many times, which wasn't checked.

some stats with the bug: 
halted: 183983 quasihalted (cycled): 192528 quashalted (lr): 762000
non-qh (cycled): 151072 non-qh (lr): 1504070 inconclusive: 150016
there were 150016 undecided machines

wxyz steps: 2000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 99239 undecided: 50777
wxyz steps: 3000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 99239 undecided: 50777
wxyz steps: 10000 proof steps: 20000 proof max_tape: 300
analyzed 150016 machines. bouncers: 99216 undecided: 50800

having fixed the bug: 
halted: 183983 quasihalted (cycled): 192528 quashalted (lr): 762000
non-qh (cycled): 151072 non-qh (lr): 1504070 inconclusive: 150016
there were 150016 undecided machines

wxyz steps: 2000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 98040 undecided: 51976
wxyz steps: 3000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 98046 undecided: 51970
wxyz steps: 10000 proof steps: 20000 proof max_tape: 300
analyzed 150016 machines. bouncers: 98020 undecided: 51996

unfixed -> fixed
2k:  99239 -> 98040 = 1199
3k:  99239 -> 98046 = 1193
10k: 99216 -> 98020 = 1196

implemented qh detection for bouncers!
there were 150016 undecided machines
wxyz steps: 10000 proof steps: 20000 proof max_tape: 300
analyzed 150016 machines. bouncers: 98020 of which QH bouncers: 6116 notQH bouncers: 91904 undecided: 51996
there were 150016 undecided machines
wxyz steps: 3000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 98046 of which QH bouncers: 6116 notQH bouncers: 91930 undecided: 51970

implemented trying multiple alignments!
before alignment
there were 150016 undecided machines
wxyz steps: 3000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 98046 of which QH bouncers: 6116 notQH bouncers: 91930 undecided: 51970
after alignment
there were 150016 undecided machines
wxyz steps: 3000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 98152 of which QH bouncers: 6116 notQH bouncers: 92036 undecided: 51864

98046 -> 98152 = +106, all of which do not QH!

after alignment
there were 150016 undecided machines
wxyz steps: 10000 proof steps: 20000 proof max_tape: 300
analyzed 150016 machines. bouncers: 98157 of which QH bouncers: 6116 notQH bouncers: 92041 undecided: 51859

98020 -> 98157 = +137, all of which do not QH

3k 
aligning -len_z to len_z instead of half that proves exactly 1 machine at 3k lol (it does not QH)
98153 / 51863 
10k 
but at 10k it proves nothing
98157 / 51859

more steps seems strictly good now - it proves 4 more machines without failing to prove any others

added truncation to the beginnings of records to see what happens and in particular whether it can 
let us solve some of the machines that take a very long time sooner
with truncation: 
there were 150016 undecided machines
wxyz steps: 3000 proof steps: 2000 proof max_tape: 100
analyzed 150016 machines. bouncers: 98160 of which QH bouncers: 6116 notQH bouncers: 92044 undecided: 51856

98153 -> 98160 = +7 LOL
wxyz steps: 3000 proof steps: 1000 proof max_tape: 100
analyzed 150016 machines. bouncers: 98160 of which QH bouncers: 6116 notQH bouncers: 92044 undecided: 51856
halving proof steps doesn't cost anything currently

wxyz steps: 1000 proof steps: 1000 proof max_tape: 100
analyzed 150016 machines. bouncers: 97939 of which QH bouncers: 6116 notQH bouncers: 91823 undecided: 52077
going down to 1k does cost us a couple hundred machines still, but not very many 

wxyz steps: 10000 proof steps: 20000 proof max_tape: 300
analyzed 150016 machines. bouncers: 98181 of which QH bouncers: 6116 notQH bouncers: 92065 undecided: 51835


better truncaction was implemented 
3k 98160 -> 98179 (+19)
from no trunctation to good truncation
10k 98157 -> 98181 (+24)
from no trunctation to mid trunctation to good truncation
10k 98157 ->(+5) 98162 ->(+19) 98181

with good truncatin
wxyz steps: 20000 proof steps: 20000 proof max_tape: 300
analyzed 150016 machines. bouncers: 98181 of which QH bouncers: 6116 notQH bouncers: 92065 undecided: 51835



1k = 97939
3k = 98179 (+221)
10k = 98181 (+2)
20k = 98181 (+0)

I did a big run to produce the canonical remaining machines file
[src/main.rs:679:3] num_lr_steps = 1000000
[src/main.rs:679:3] num_rule_steps = 200
tnf machines 1000000
tnf machines 2000000
halted: 183983 quasihalted (cycled): 192528 quashalted (lr): 762025
non-qh (cycled): 151072 non-qh (lr): 1504341 inconclusive: 149720
there were 149720 undecided machines
wxyz steps: 10000 proof steps: 20000 proof max_tape: 300
analyzed 149720 machines. bouncers: 98181 of which QH bouncers: 6116 notQH bouncers: 92065 undecided: 51539
wrote 51539 machines to file: machine_lists/size4_bouncer_aligned_truncated_10k_20k_300_23_august_24

149720 down to 51539! ~3x, 2.905 to be specific