# Proof Theory of Skew Closed and Skew Prounital Closed Categories

The code includes several equivalent presentations of the free skew closed category on a set of generators:
- a Hilbert-style calculus of combinators ([code-skewclosed/FreeSkewClosed.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/FreeSkewClosed.agda))
- a cut-free sequent calculus ([code-skewclosed/SeqCalc.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/SeqCalc.agda))
- a focused subsystem of sequent calculus derivations ([code-skewclosed/Focusing.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/Focusing.agda))
- a term calculus/natural deduction style calculus and a proof of normalization by hereditary substitutions ([code-skewclosed/HeredSubs.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/HeredSubs.agda))

The main file containing the whole development for the skew closed case is [code-skewclosed/Everything.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/Everything.agda).

The code also contains an analogous development for skew prounital closed categories (in which the unit is not represented).
The main file containing the whole development for the skew prounital closed case is [code-skewprounitalclosed/Everything.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed/Everything.agda).

The formalization uses Agda 2.6.0. 
