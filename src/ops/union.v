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
  rewrite /repr.
  rewrite -setP.
  rewrite /eq_mem=> x.
  rewrite in_setU.
  rewrite /union /orB.
  rewrite HE HE'.
  have H: forall (P: ordinal_finType n -> bool),
      (x \in [ set x0 | P x0 ]) = (P x)
      by admit.
  rewrite !H.
  rewrite getBit_liftBinOp //.
Admitted.
