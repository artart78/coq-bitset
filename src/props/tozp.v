From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.

Lemma toZp_shlBn:
  forall n (p: BITS n) k, k < n ->
    toZp (shlBn p k) = (toZp p * (2 ^ k)%:R)%R.
Proof.
  move=> n p k le_k.
  elim: k le_k=> [|k IHk] le_k.
  + (* Case: k ~ 0 *)
    rewrite /shlBn /=.
    by rewrite expn0 GRing.mulr_natr //.
  + (* Case: k ~ k + 1 *)
    rewrite /shlBn iterS -[iter k shlB p]/(shlBn _ _).
    rewrite toZp_shlB.
    rewrite IHk; last by auto with arith.
    rewrite expnS.
    rewrite mulnC.
    rewrite !GRing.mulr_natr.
    rewrite GRing.mulrnA //.
Qed.

