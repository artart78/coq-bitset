From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun.
From MathComp
     Require Import tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Definition symdiff {n} (bs: BITS n) (bs': BITS n): BITS n
  := xorB bs bs'.

Lemma symdiff_repr:
  forall n (bs: BITS n) (bs': BITS n) E E', repr bs E -> repr bs' E' ->
    repr (symdiff bs bs') ((E :\: E') :|: (E' :\: E)).
Proof.
  move=> n bs bs' E E' HE HE'.
  rewrite /repr -setP /eq_mem=> x.
  rewrite in_setU !in_setD.
  rewrite /symdiff /xorB HE HE' !in_set getBit_liftBinOp=> //.
  case: (getBit bs x)=> //.
  + (* getBit bs x = true *)
    by rewrite andbT orbF Bool.xorb_true_l.
  + (* getBit bs x = false *)
    by rewrite andbF orbC orbF andbC andbT Bool.xorb_false_l.
Qed.
