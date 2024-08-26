Known species!

Solved/solvable: 
Halters
Cyclers/translated cyclers
1 stage bouncer

currently unsolved: 
two_stage bouncer
counter
three_stage bouncer
translated bouncer with shadow 
midpoint bouncer 
cubic bouncer 
fast tail eating dragon 

counts
total machines: 2_943_669
halters: 183_393 (6.23%)
cyclers: 343_600 (11.7%)
TC: 2_266_070 (77.0%)
cycler/TC: 2_609_670 (88.7%)
1 stage bouncer: 100_267 (3.41%)
unsolved: 49749 (1.69%)

unsolved is 1 in 59

estimated proportions unsolved, via a classification of 40 machines
17 (43%)  two_stage 
13 (33%)  counter
4  (10%) three_stage 
4  (10%) translated bouncer with shadow 
1  (2.5%) midpoint bouncer 
1  (2.5%) fast tail eating dragon 

to get overall estimated percentages, we divide by 59: 
0.80%  two_stage 
0.61%  counter
0.19%  three_stage 
0.19%  translated bouncer with shadow 
0.047% midpoint bouncer 
0.047% fast tail eating dragon 
but these are of course highly uncertain. 


Description of species
Solved/solvable: 

Halters
Halts at a finite time. 

Cyclers
enters the same (state, tape) as previously visited within some finite time

translated cyclers

`exists a b S. such that a b<S 0* -> a a b<S 0* after some finite time`

and 
`exists x such that 0*<A 0* -> 0* x a b<S 0* `
(or the mirror image thereof)
in GoL terminology, the machine is a "puffer". 
in words, the machine repeats the same series of actions at the edge of the tape over and over 
and only fails to actually cycle because it emits some "waste" never to be read again each time

equivalently, the machine repeats the exact series of transitions starting at the edge of 
the tape _twice_. 


1 stage bouncer
informally: 
```
 X  Z^n     Y<
>X' Z'^n    Y'
 X  Z^(n+1) Y<
```
(the machine only traverses leftwards once and rightwards once during this cycle)

currently unsolved: 
two_stage bouncer
```
 X    Z^n     Y<
>X'   Z'^n    Y'
 X''  Z''^n   Y''<
>X''' Z'''^n  Y'''
 X    Z^(n+1) Y<
 ```
(the machine traverses leftwards, rightwards, leftwards, rightwards, and then cycles)

counter
there exists 0 and 1 which equal some base-turing machine string, eg FT and FF
letting bin(n) be the binary representation of n, eg bin(5) = 101
```
0* bin(n) <  0*
0* bin(n+1)< 0*
```
for all n; and in particular the machine does this in some well-specified cellular automaton 
way that I haven't written up here. 

configs with
A >T< 
2275 

three_stage bouncer
generalization of 1 and 2 stage bouncer to 3 stages. in general k-stage bouncers exist for 
any k, though k>3 has not been found in this search space yet. 


translated bouncer with shadow 
```
X A^n Y B^n Z<
X A^(n+1) Y B^(n+1) Z<
```
via 
```
X A^n Y   B^n   Z<
X A^n >Y' B'^n  Z'
X A^n Y'' B''^n Z''<
=
X A^(n+1) Y B^(n+1) Z<
```
like a bouncer, but grows 2 things repeatedly by going left, then right, over only the right (or left) thing. 
(there exists a variant of this where it leaves no shadow, which with the right sorts of upgrades is not 
*too* hard to prove using a normal 1-stage bouncer prover)


midpoint bouncer 
```
X A^n Y B^n Z<
X A^(n+1) Y B^(n+1) Z<
```
via
```
X   A^n   Y   B^n   Z<
>X' A'^n  Y'  B'^n  Z'
X'' A''^n Y'' B''^n Z''<
=
X A^(n+1) Y B^(n+1) Z<
``` 
like a bouncer, but grows 2 things repeatedly by going left, then right over both things. 


these two machines are the first to have "multiple levels" of cycles, where 
there's a subcycle executed N times for some N, and then that overall gets repeated
infinitely
cubic bouncer 
```
cycle 1
X A^n     B^m     Y<
X A^(n-1) B^(m+1) Y<
via 
X A^n     B^m     Y<
X A^(n-1) >A' B^m Y
X A^(n-1) B^(m+1) Y<
```
goes left once, then goes right, converts 1 A to 1 B by doing this, does not grow 
the live area of the tape during cycle 1 

```
cycle 2
X A^n     Y<
X A^(n+1) Y<
via
X   A^n     Y< (n applications of cycle 1)
X   B^n     Y< 
>X' C^n     Y
X   A^(n+1) Y<
```
appllies cycle 1 n times, then does ~a bouncer cycle, modulo 
converting Bs back into As. 
example transcript: 
X A A A Y
X B A A Y
X B B A Y
X B B B Y 
X A A A A Y

fast tail eating dragon 
so this is similar to the previous, but cycle 1 grows the tape to the right, 
so the transcript looks fairly different, 
but the music-notation / transition sequence looks ~similar
example transcript
```
cycle 1
>X B B A  A Y 
 X B B A< A Y 
X< B B B  A Y
>X B B B B  A Y

cycle 2
>X A A A Y
>X B B A A Y
>X B B B B A Y  
>X B B B B B B Y
>X A A A A A A A Y
```

```
cycle 1
>X B^n   A
X  B^n   A<
X< B^n   B
>X B B^n B

cycle 2
>X   B^n     Y
X'   B'^n    Y'<
>X'' B''^n   Y''
=
X    A^(n+k) Y
```
for some global constant k likely small


todo: include examples of each of these in the zoology

Solved/solvable: 
Halters
Cyclers/translated cyclers
1 stage bouncer 1RB0RD_1LC1LC_1RA1LB_0LB1LC

currently unsolved: 
two_stage bouncer 1RB0RC_1RC1LC_1LA1LD_1RA1LB
counter 1RB1RC_0LC1LA_0LB1RD_1LB0RD
three_stage bouncer 1RB0RD_1LC0LC_0RD1LB_1RB1RA
translated bouncer with shadow 1RB---_1LC1RD_1LC1RB_0RC0RD
midpoint bouncer 1RB0LC_1LC1RB_1LA0LD_0RB1RD
cubic bouncer 
fast tail eating dragon  1RB0LD_1LC0RA_0RD1LB_1RD1LA
