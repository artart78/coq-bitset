Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

(** * Set complement  *)

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
