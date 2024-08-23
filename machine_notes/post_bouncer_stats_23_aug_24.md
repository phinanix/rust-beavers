"machine_lists/size4_bouncer_aligned_truncated_10k_20k_300_23_august_24",

analyzing random machines from the 51539 machines left after bouncers are removed

0 1RB1LD_1LC0RD_1LA0RB_1LC1RC
two_stage 
1 1RB1RA_1LC1LD_0RA1RB_1LA1LB
two_stage
2 1RB1LA_1LC1RD_1LA0LC_1LA0RA
two_stage
3 1RB1RC_0LC1LA_0LB1RD_1LB0RD
counter
4 1RB0LD_0LB1RC_1LA1RB_0RA1RB
two_stage
5 1RB0RD_1RC0LD_1LA0RC_0LA1LD
counter
6 1RB1RD_1RC0LC_1LA1LA_1LC0RD
counter
7 1RB1LD_1LC1RB_0RC1LA_0LC0LC
counter
8 1RB0LD_1RC1LD_0LA0RC_0RD1LB
counter
9 1RB0LC_0LC1RA_0RA1LD_1LC0RC
counter
10 1RB1LB_1LC0RD_1RA0LB_1RB1RA
two_stage
11 1RB0RD_0LC1RB_1LD1LA_1LA1LC
two_stage
12 1RB1RC_1LA1RC_1LD0RB_0RA0LD
counter
13 1RB1LD_0LC0RB_1LA1LC_1LC1RD
counter
14 1RB1LD_1RC1RD_0LA1RD_1RB0LA
two_stage
15 1RB1RA_0LC1LD_0LD1LC_1RD0RA
translated bouncer with shadow
16 1RB1LA_1RC0LC_0RD0LA_1LA0RD
counter
17 1RB1RA_1LC1LD_1RC0LB_0RA1LD
two_stage
18 1RB0RC_1LC1RB_1LB1LD_0RB0LA
two_stage
19 1RB1LC_0LA1RC_1RB1LD_0LC0RC
two_stage
20 1RB0LD_1LC0RA_0RD1LB_1RD1LA
fast tail eating dragon
21 1RB0RC_1RC1LC_1LA1LD_1RA1LB
two_stage
22 1RB1RB_0RC1RA_1RD0LD_1LC1LB
two_stage
23 1RB---_1LC1RD_1LC1RB_0RC0RD
translated bouncer with shadow
24 1RB1LC_1LB0RC_1LD1LA_0LA---
translated bouncer with shadow

total 
12 two_stage 9 counter 
3 translated bouncer with shadow 1 fast tail eating dragon

aggregating with results from 2 aug 24: 
9 grows_left 5 two_stage 4 three_stage 4 counter 
1 midpoint bouncer 1 translated bouncer with shadow 1 cubic bouncer
9 grows_left = 9/25 = 36%, diff in bouncers from then to now: 51539 / 62127 = 83%; 1-x = 17%, oof. 

dropping grows left gives 16 machines and 25 machines
5 two_stage 4 three_stage 4 counter 
1 midpoint bouncer 1 translated bouncer with shadow 1 cubic bouncer
12 two_stage 9 counter 
3 translated bouncer with shadow 1 fast tail eating dragon
total
17 two_stage 4 three_stage 13 counter (34)
4 translated bouncer with shadow 1 midpoint bouncer 1 cubic bouncer 1 fast tail eating dragon (7)
41 total
7 categories
13/41 = est 32% counters
ie est. remaining counters are 51539 * 13/41 = 16342
var = n*p(1-p) = 41 * (.32*.68) = 41 * .2176 = 8.9
std_dev = 2.99
rel_err = 3/41 = 7%

17 (41%)  two_stage 
13 (32%)  counter
4  (9.8%) three_stage 
4  (9.8%) translated bouncer with shadow 
1  (2.4%) midpoint bouncer 
1  (2.4%) cubic bouncer 
1  (2.4%) fast tail eating dragon 
41 total

