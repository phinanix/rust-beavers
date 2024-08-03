sampled 25 machines from size4_bouncer_not_quite_qh_holdouts_2_august_24
which are the things that would be qh holdouts if the bouncer decider decided quashalting, which it does not
and also it only has LR run for 1K steps, not 1M, but that only affects 296 machines

results 
9 grows_left 5 two_stage 4 three_stage 4 counter  (22)
(36%) (36% multi) (20%)      (16%)       (16%)
1 midpoint bouncer 1 translated bouncer with shadow 1 cubic bouncer
(4% each)
25 total

decreasing by 2.4x to put in frame of 30jul24 file:
15% multi
6.67% counter
1.67% midpoint bouncer
5% "not bouncer or counter"

single pass bouncers decided by program: 87889
estimated undecided grows_left: 22366
estimated total bouncers: 110255
estimated percent that grow left: 20%

copying results: of the random machines from the list undecided_size_4_random_100
4 counter 3 two_sweep 2 left_grow 1 translated_no_shadow
however these had a bunch of bouncers already filtered, so it's not really a fair comparison

size4 

1RB0RD_1LC1LC_1RA1LB_0LB1LC
1RB1RC_1LA0LA_1RA1LD_0RA0LC
1RB0RD_1LC0LC_0RD1LB_1RB1RA
1RB1RD_0LC0RB_1LC1LD_1RA1RB
1RB1RD_0LB1LC_0LD0LA_1RC1LD
1RB0LD_1RC0RA_1LA0LC_1LA1LC
1RB1LD_1RC0RB_1LA0RC_0LD0RC
1RB0LD_0RC1RB_1RD0RD_1LA0RC
1RB1RA_0LC0LB_1RD1LC_1LA0RD
1RB0LB_1RC1LD_0LA0RC_0LA0LB
1RB1LA_0LC0RD_1LA0RD_0LC1LA
1RB1LA_0LC0RA_1RA1LD_0LC0RA
1RB1RB_1LC1RD_0LB1LA_1LB0RD
1RB1LC_1LA0RC_1LD0LA_1RD1RB
1RB0RA_0LC---_1LD0LC_1RA1LD
1RB1LC_1RC1RD_0LA1LB_0RB0RB
1RB1RB_1RC1LC_0LD0LA_0RB1LD
1RB0LD_1RC1LA_1LD1RB_1RB1LC
1RB0LD_1LC0RA_0LD0RD_1LA0LC
1RB0LD_0LC1RA_1RC1LA_0LB0LD
1RB0LC_1LC1RB_1LA0LD_0RB1RD
1RB1RC_1LC1RC_1LD1RA_0RB1LD
1RB1RA_1LC1RD_0RA1LD_1RA0LC
1RB1LC_0LA0RD_1RA1LD_1RC0LC
1RB1LA_1LC0RD_1RA0RB_0RB1RD


0 1RB0RD_1LC1LC_1RA1LB_0LB1LC
bouncer: grows_left
1 1RB1RC_1LA0LA_1RA1LD_0RA0LC
bouncer: two_stage
2 1RB0RD_1LC0LC_0RD1LB_1RB1RA
bouncer: three_stage
3 1RB1RD_0LC0RB_1LC1LD_1RA1RB
bouncer: three_stage
4 1RB1RD_0LB1LC_0LD0LA_1RC1LD
bouncer: grows_left
5 1RB0LD_1RC0RA_1LA0LC_1LA1LC
bouncer: three_stage
6 1RB1LD_1RC0RB_1LA0RC_0LD0RC
counter
7 1RB0LD_0RC1RB_1RD0RD_1LA0RC
cubic bouncer
8 1RB1RA_0LC0LB_1RD1LC_1LA0RD
counter
9 1RB0LB_1RC1LD_0LA0RC_0LA0LB
bouncer: grows_left
10 1RB1LA_0LC0RD_1LA0RD_0LC1LA
bouncer: grows_left 
11 1RB1LA_0LC0RA_1RA1LD_0LC0RA
bouncer: two_stage
12 1RB1RB_1LC1RD_0LB1LA_1LB0RD
counter
13 1RB1LC_1LA0RC_1LD0LA_1RD1RB
bouncer: grows_left
14 1RB0RA_0LC---_1LD0LC_1RA1LD
counter
15 1RB1LC_1RC1RD_0LA1LB_0RB0RB
bouncer: two_stage
16 1RB1RB_1RC1LC_0LD0LA_0RB1LD
bouncer: grows_left
17 1RB0LD_1RC1LA_1LD1RB_1RB1LC
bouncer: two_stage
18 1RB0LD_1LC0RA_0LD0RD_1LA0LC
bouncer: grows_left
19 1RB0LD_0LC1RA_1RC1LA_0LB0LD
bouncer: grows_left
20 1RB0LC_1LC1RB_1LA0LD_0RB1RD
bouncer: midpoint (one_stage) (ie tape looks like X Y^n Z^n W)
21 1RB1RC_1LC1RC_1LD1RA_0RB1LD
bouncer: two_stage
22 1RB1RA_1LC1RD_0RA1LD_1RA0LC
bouncer: three_stage
23 1RB1LC_0LA0RD_1RA1LD_1RC0LC
bouncer: grows_left
24 1RB1LA_1LC0RD_1RA0RB_0RB1RD
translated bouncer with shadow

9 grows_left 5 two_stage 4 three_stage 4 counter  (22)
1 midpoint bouncer 1 translated bouncer with shadow 1 cubic bouncer
25 total
