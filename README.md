# Deductive Systems and Coherence for Skew (Prounital) Closed Categories

The code includes several equivalent presentations of the free skew prounital closed category on a set of generators:
- a categorical calculus (Hilbert style) ([code-skewprounitalclosed/FreeSkewProunitalClosed.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed/FreeSkewProunitalClosed.agda))
- a cut-free sequent calculus ([code-skewprounitalclosed/SeqCalc.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed/SeqCalc.agda))
- a focused subsystem of sequent calculus derivations ([code-skewprounitalclosed/Focusing.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed/Focusing.agda))
- a natural deduction calculus and a proof of normalization by hereditary substitutions ([code-skewprounitalclosed/HeredSubs.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed/HeredSubs.agda))
- normalization by evaluation for the natural deduction calculus ([code-skewprounitalclosed/NbE.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed/NbE.agda))

The main file containing the whole development for the skew prounital closed case is [code-skewprounitalclosed/Everything.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed/Everything.agda).

The code also contains a categorical calculus and an equivalent cut-free sequent calculus presenting the free skew prounital closed category on a skew multicategory, that avoids left-normality. See the main file [code-skewprounitalclosed-skewmult/Everything.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewprounitalclosed-skmult/Everything.agda) (this file takes ~2 hours to typecheck on a Dell Latitude 7400 with 1.9 GHz Intel Core i7) 

The code also contains an analogous development for skew closed categories (i.e. with a represented unit I).
The main file in this case is [code-skewclosed/Everything.agda](https://github.com/niccoloveltri/skewclosedcats/blob/master/code-skewclosed/Everything.agda).

The formalization uses Agda 2.6.0. 
