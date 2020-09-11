# Proof Theory of Skew Closed Categories

The code includes several equivalent presentations of the free skew closed category on a set of generators:
- a Hilbert-style calculus of combinators ([FreeSkewClosed.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/FreeSkewClosed.agda))
- a cut-free sequent calculus ([SeqCalc.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/SeqCalc.agda))
- a focused subsystem of sequent calculus derivations ([Focusing.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/Focusing.agda))
- a term calculus/natural deduction style calculus and a proof of normalization by hereditary substitutions ([HeredSubs.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/HeredSubs.agda))

The formalization uses Agda 2.6.0. 
The main file containing the whole development is [Everything.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/Everything.agda).
