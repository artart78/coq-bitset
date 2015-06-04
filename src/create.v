From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.

Definition create {n} (b: bool): BITS n
  := if b then dropmsb (subB (shlBn (n := n.+1) #1 n) #1) else #0.

Import GRing.

Lemma toZp_shlBn:
  forall n (p: BITS n) k, k < n ->
    toZp (shlBn p k) = (toZp p * (2 ^ k)%:R)%R.
Proof.
  move=> n p k le_k.
  elim: k le_k=> [|k IHk] le_k.
  + (* Case: k ~ 0 *)
    rewrite /shlBn /=.
    by rewrite expn0 mulr_natr //.
  + (* Case: k ~ k + 1 *)
    rewrite /shlBn iterS -[iter k shlB p]/(shlBn _ _).
    rewrite toZp_shlB.
    rewrite IHk; last by auto with arith.
    rewrite expnS.
    rewrite mulnC.
    rewrite !mulr_natr.
    rewrite mulrnA //.
Qed.

Lemma makeOnes:
  forall n,
    joinmsb (false, ones n) = subB (shlBn (n := n.+1) #1 n) #1.
Proof.
  move=> n.
  apply toZp_inj.
  have ->: joinmsb (false, ones n) = fromNat (n:=n.+1) (toNat (joinmsb (false, ones n))) by rewrite toNatK.
  rewrite toNat_joinmsb0 toNat_ones.
  rewrite toZp_fromNat.
  autorewrite with ZpHom.
  rewrite toZp_shlBn.
  autorewrite with ZpHom.
  rewrite !mulr_natr.
  rewrite -subn1.
  rewrite natrB.
  rewrite mulr1n //.
  rewrite expn_gt0 //.
  auto with arith.
Qed.

Lemma create_repr:
  forall n (b: bool), n > 0 ->
    create b = if b then ones n else spec.zero n.
Proof.
  move=> n b gtz_n.
  have ->: ones n = dropmsb (joinmsb (false, ones n)) by rewrite dropmsb_joinmsb.
  rewrite makeOnes /create fromNat0 //.
Qed.
