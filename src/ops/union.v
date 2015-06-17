From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import props.getbit spec.

Definition union {n} (bs: BITS n) (bs': BITS n): BITS n
  := orB bs bs'.

Lemma union_repr:
  forall n (bs: BITS n) (bs': BITS n) E E', repr bs E -> repr bs' E' ->
    repr (union bs bs') (E :|: E').
Proof.
  move=> n bs bs' E E' HE HE'.
  rewrite /repr -setP /eq_mem=> x.
  by rewrite in_setU /union /orB HE HE' !in_set getBit_liftBinOp.
Qed.
