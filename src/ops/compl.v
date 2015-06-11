From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import props.getbit spec.

Definition compl {n} (bs: BITS n): BITS n
  := invB bs.

Lemma compl_repr:
  forall n (bs: BITS n) E, repr bs E ->
    repr (compl bs) (~: E).
Proof.
  move=> n bs E HE.
  rewrite /repr -setP /eq_mem=> x.
  by rewrite in_setC HE !in_set getBit_liftUnOp.
Qed.
