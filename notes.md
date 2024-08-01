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

- write "spec" / alg for bouncer decider
- implement bouncer decider