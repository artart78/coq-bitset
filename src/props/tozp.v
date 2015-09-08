From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.

(* TODO: this shall eventually be moved to coq-bits:operations/properties.v *)


Lemma toZp_shlBn:
  forall n (p: BITS n) k, k < n ->
    toZp (shlBn p k) = (toZp p * (2 ^ k)%:R)%R.
Proof.
  move=> n p.
  elim=> [|k IHk] le_k.
  + (* Case: k ~ 0 *)
    by rewrite expn0 GRing.mulr_natr //.
  + (* Case: k ~ k + 1 *)
    rewrite /shlBn iterS -[iter k shlB p]/(shlBn _ _).
    rewrite toZp_shlB.
    rewrite IHk; last by auto with arith.
    by rewrite expnS mulnC !GRing.mulr_natr GRing.mulrnA.
Qed.

Lemma toNat_shlBn:
  forall n k, k < n -> toNat (shlBn (n := n) #1 k) = 2 ^ k.
Proof.
  move=> n.
  elim=> [le_k|k IHk le_k].
  + (* k ~ 0 *)
    rewrite toNat_fromNat modn_small=> //.
    have {1}->: 1 = 2 ^ 0 by trivial.
    by rewrite ltn_exp2l.
  + (* k ~ k.+1 *)
    rewrite toNat_shlB IHk.
    rewrite -muln2.
    have {2}->: 2 = 2 ^ 1 by trivial.
    rewrite -expnD addn1 modn_small // ltn_exp2l //.
    auto with arith.
Qed.
