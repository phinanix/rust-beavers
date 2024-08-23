
playing with bouncers with different stats

loaded 50777 machines from f1 size4_bouncer_2k_2k_100_22_august_24
loaded 50800 machines from f2 size4_bouncer_10k_20k_300_22_august_24
there were 50720 machines in both files, 57 machines in f1 only 80 machines in f2 only
wrote 57 machines to file: size4_bounce_proven_only_10k_22_aug_24
wrote 80 machines to file: size4_bounce_proven_only_2k_22_aug_24



this bouncer was solved at 10k but not at 2k
1RB---_0LC0RD_0RA1LB_1LD0LC
it's deal is that when traversing right it follows the rule
C >F<FTTTF
C FT>F<FTT
but during one bounce, it only increases the size of the tape by 2, so we guess 
that it follows some rule shaped like
SS>SS -> SSSS>
and it does not. 
so how the heck does it work at 10k?
10k 20k 300
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 FT z2 TF
step: 0 state: B tape: FT>T<F
step: 1 state: D tape: FTF>F<
step: 2 state: D tape: FT>F<T
step: 3 state: D tape: F>T<TT
step: 4 state: C tape: >F<FTT
step: 5 state: A tape: F>F<TT
step: 6 state: B tape: FT>T<T
step: 7 state: D tape: FTF>T<
step: 8 state: C tape: FT>F<F
step: 9 state: A tape: FTF>F<
step: 10 state: B tape: FTFT>F<
mbz4z3 FTFT
z4 FT mb_z3 FT

2k 2k 100
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 TF z2 FT
step: 0 state: D tape: TF>F<T
step: 1 state: D tape: T>F<TT
step: 2 state: D tape: >T<TTT
step: 3 state: C tape: >F<FTTT
mb proof: Err: fell wrong way step 4

man this is some kind of cursed alignment issue, isn't it!
anyway it definitely seems solved by doubling the length of z, I think. 
.. or it isn't
wxyz steps: 2000 proof steps: 2000 proof max_tape: 100
w:  x: FTFTFTFTFTFTFT y: FTFTFTFTFTFTFTF z: FT
wxyz steps: 10000 proof steps: 20000 proof max_tape: 300
w:  x: FTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTF y: TFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTF z: TF
okay, so it's an issue where it's FT versus TF, it would seem?
doubling the length of z fucks everything though, I was about to say, I don't understand why, but I guess I do. 
it's because with a double length z, you'd have to run the whole cycle *twice* for it to come back around. 
Which I somehow hadn't thought of until now. 

What I actually still don't get though, is why it would be the case that we get a different Z in the one case 
versus the other case. oh again yeah it's some kind of cursed alignment issue. 
at 10k z4 was TFTFTFTF
at 2k z4 was FTFTFTFT


idx 1
just ran machine: 1RB0RA_1LC0RD_0RA0LB_1LD0LC
2k w:  x: FFTFTFTFTFTFTF y: TFTFTFTFTFTFTFF z: TF
10k w:  x: FFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFT y: FTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFF z: FT
seems same

idx 2
just ran machine: 1RB1LC_0RC---_1RD0LA_0LA1RD
2k  
len w: 0 len x: 14 len y: 15 len z: 2
w:  x: TTTTTTTTTTTTTT y: TTTTTTTTTTTTFTF z: TT
10k 
len w: 0 len x: 37 len y: 38 len z: 2
w:  x: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT y: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTFTF z: TT
these seem pretty samey to me, weird
but it's going to be some parity alignment thingy again I can tell
due to like len x and len y or something
10k 
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 FT z2 TF
step: 0 state: D tape: FT>T<F
step: 1 state: D tape: FTT>F<
step: 2 state: A tape: FT>T<F
step: 3 state: C tape: F>T<TF
step: 4 state: A tape: >F<FTF
step: 5 state: B tape: T>F<TF
step: 6 state: C tape: TF>T<F
step: 7 state: A tape: T>F<FF
step: 8 state: B tape: TT>F<F
step: 9 state: C tape: TTF>F<
step: 10 state: D tape: TTFT>F<
mbz4z3 TTFT
z4 TT mb_z3 FT
2k 
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 TT z2 FT
step: 0 state: D tape: TT>F<T
step: 1 state: A tape: T>T<FT
step: 2 state: C tape: >T<TFT
step: 3 state: A tape: >F<FTFT
mb proof: Err: fell wrong way step 4
yeah this is the same off-by-one alignment bullshit this time with z2 = TF or z2 = FT

idx 3
just ran machine: 1RB0RA_1LC0RD_0RA0LB_1LD0LC

2k
len w: 0 len x: 14 len y: 15 len z: 2
w:  x: FFTFTFTFTFTFTF y: TFTFTFTFTFTFTFF z: TF
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 TF z2 FT
step: 0 state: D tape: TF>F<T
step: 1 state: D tape: T>F<TT
step: 2 state: D tape: >T<TTT
step: 3 state: C tape: >F<FTTT
mb proof: Err: fell wrong way step 4

10k
len w: 0 len x: 37 len y: 38 len z: 2
w:  x: FFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFT y: FTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFF z: FT
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 FT z2 TF
step: 0 state: B tape: FT>T<F
step: 1 state: D tape: FTF>F<
step: 2 state: D tape: FT>F<T
step: 3 state: D tape: F>T<TT
step: 4 state: C tape: >F<FTT
step: 5 state: A tape: F>F<TT
step: 6 state: B tape: FT>T<T
step: 7 state: D tape: FTF>T<
step: 8 state: C tape: FT>F<F
step: 9 state: A tape: FTF>F<
step: 10 state: B tape: FTFT>F<
mbz4z3 FTFT
z4 FT mb_z3 FT

yeah same cursed alignment issue

idx 4
2k
len w: 0 len x: 16 len y: 16 len z: 2
w:  x: FFTFTFTFTFTFTFTF y: TFTFTFTFTFTFTFTF z: TF
step 2   sim Z < Z1 -> < Z1 Z2
z TF z1 FT
step: 0 state: A tape: T>F<FT
step: 1 state: B tape: TT>F<T
step: 2 state: C tape: TTT>T<
step: 3 state: C tape: TTTT>F<
mb proof: Err: fell off the wrong side step 2



10k
len w: 0 len x: 41 len y: 41 len z: 2
w:  x: FFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFT y: FTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTF z: FT
step 2   sim Z < Z1 -> < Z1 Z2
z FT z1 TF
step: 0 state: D tape: F>T<TF
step: 1 state: A tape: >F<FTF
step: 2 state: B tape: T>F<TF
step: 3 state: C tape: TT>T<F
step: 4 state: C tape: TTT>F<
step: 5 state: A tape: TT>T<F
step: 6 state: D tape: T>T<TF
step: 7 state: A tape: >T<FTF
step: 8 state: D tape: >F<TFTF
mbz1z2 TFTF z1 TF
mbz1z2 TFTF z2 TF

same alignment issue

idx 5
just ran machine: 1RB0LB_0RC1RA_0LC1LD_1LA0LC

2k 
len w: 0 len x: 14 len y: 15 len z: 2
w:  x: TTTTTTTTTTTTTT y: TTTTTTTTTTTTTFF z: TT
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 TF z2 TF
step: 0 state: C tape: TF>T<F
step: 1 state: D tape: T>F<TF
step: 2 state: A tape: >T<TTF
step: 3 state: B tape: >F<FTTF
mb proof: Err: fell wrong way step 4

10k 
len w: 0 len x: 37 len y: 38 len z: 2
w:  x: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT y: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTFF z: TT
step 4   sim Z3 > Z2 -> Z4 Z3 >
z3 TT z2 FT
step: 0 state: B tape: TT>F<T
step: 1 state: C tape: TTF>T<
step: 2 state: D tape: TT>F<T
step: 3 state: A tape: T>T<TT
step: 4 state: B tape: >T<FTT
step: 5 state: A tape: T>F<TT
step: 6 state: B tape: TT>T<T
step: 7 state: A tape: TTT>T<
step: 8 state: B tape: TT>T<F
step: 9 state: A tape: TTT>F<
step: 10 state: B tape: TTTT>F<
mbz4z3 TTTT
z4 TT mb_z3 TT

skipped idx 6,7 cause they looked same
idx 8
just ran machine: 1RB1LC_0RC0RA_1LD1RD_0LA0LB
this is a bouncer that only starts bouncing at step 1267 !
before that it's kind of fast-tail-eating-dragon like
so it actually needs the additional length !
only 2447 total length though - I checked and it is solved at 3k

idx 9
3k
just ran machine: 1RB0RD_0LC0RB_1RA1LC_1LD1LB
tape extents: [6, 8, 9, 14, 20, 26, 33, 36, 43, 48, 57, 63]
tape diffs  : [2, 1, 5, 6, 6, 7, 3, 7, 5, 9, 6]
mb len z: None
couldn't find a len for z
mb proof: Err: couldn't find a len for z
I'm guessing this one also needs additional time!
10k
tape extents: [6, 8, 9, 14, 20, 26, 33, 36, 43, 48, 57, 63, 68, 73, 78, 83, 88, 93, 98, 103, 108, 113, 118, 123, 128, 133, 138, 143]
tape diffs  : [2, 1, 5, 6, 6, 7, 3, 7, 5, 9, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]
mb len z: Some(5)
and then it all just works! so it doesn't start bouncing until tape 63 = step 2849
so we need tape 78 = step 3698 to solve it!

idx 10
just ran machine: 1RB1LB_1RC1LC_0LD0RD_1LD0LA

2k
step 2   sim Z < Z1 -> < Z1 Z2
z TT z1 TT
step: 0 state: C tape: T>T<TT
step: 1 state: D tape: TF>T<T
step: 2 state: A tape: T>F<FT
step: 3 state: B tape: TT>F<T
step: 4 state: C tape: TTT>T<
step: 5 state: D tape: TTTF>F<
mb proof: Err: fell off the wrong side step 2
TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTF
len w: 0 len x: 13 len y: 14 len z: 2

10k
step 2   sim Z < Z1 -> < Z1 Z2
z TT z1 TF
step: 0 state: B tape: T>T<TF
step: 1 state: C tape: >T<TTF
step: 2 state: D tape: F>T<TF
step: 3 state: A tape: >F<FTF
step: 4 state: B tape: T>F<TF
step: 5 state: C tape: TT>T<F
step: 6 state: D tape: TTF>F<
step: 7 state: D tape: TT>F<T
step: 8 state: D tape: T>T<TT
step: 9 state: A tape: >T<FTT
step: 10 state: B tape: >F<TFTT
mbz1z2 TFTT z1 TF
mbz1z2 TFTT z2 TT
len w: 0 len x: 34 len y: 35 len z: 2
w:  x: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT y: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTF z: TT

idx 11,12 appeared to also be parity 

idx 13
just ran machine: 1RB0LA_1LC1RD_1LA1LC_1LA0RB

mb proof: Err: z1z2 didn't start with z1

len w: 0 len x: 25 len y: 25 len z: 6
w:  x: TTFTFTFTFTFTFTFTFTFTFTFTF y: TFTFTFTFTFTFTFTFTFTFTFTFF z: TFTFTF

step 2   sim Z < Z1 -> < Z1 Z2
z TFTFTF z1 FTTTTT
step: 0 state: A tape: TFTFT>F<FTTTTT
step: 1 state: B tape: TFTFTT>F<TTTTT
step: 2 state: C tape: TFTFT>T<TTTTTT
step: 3 state: C tape: TFTF>T<TTTTTTT
step: 4 state: C tape: TFT>F<TTTTTTTT
step: 5 state: A tape: TF>T<TTTTTTTTT
step: 6 state: A tape: T>F<FTTTTTTTTT
step: 7 state: B tape: TT>F<TTTTTTTTT
step: 8 state: C tape: T>T<TTTTTTTTTT
step: 9 state: C tape: >T<TTTTTTTTTTT
step: 10 state: C tape: >F<TTTTTTTTTTTT
mbz1z2 TTTTTTTTTTTT z1 FTTTTT
mb proof: Err: z1z2 didn't start with z1

if seems like maybe this guy isn't a bouncer at all for the first bit?
or is a 3 stage bouncer or something ???
10k 
len w: 0 len x: 76 len y: 76 len z: 6
w:  x: TTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFT y: FTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFF z: FTFTFT

wait okay I'm not convinced at all this guy is actually a bouncer ???
rather than like a 3 stage bouncer for example

w:  x: TT FTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFT FT y: FTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFTFT FTFF z: FTFTFT

wxyz steps: 400 proof steps: 2000 proof max_tape: 100
len w: 0 len x: 4 len y: 4 len z: 6
w:  x: TTFT y: FTFF z: FTFTFT
mb proof: BouncerProof w:  x: TTFT y: FTFF z: FTFTFT state_0: B 

config: TTFT FTFTFT FTFF<B
