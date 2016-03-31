Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

(** * Set complement  *)
Definition compl {n} (bs: BITS n): BITS n := invB bs.

Lemma compl_repr n (bs: BITS n) E :
  repr bs E -> repr (compl bs) (~: E).
Proof. by move->; apply/setP=> i; rewrite !inE getBit_liftUnOp. Qed.
