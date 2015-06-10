From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.
Require Import tozp getbit.

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
  rewrite !GRing.mulr_natr.
  rewrite -subn1.
  rewrite GRing.natrB.
  rewrite GRing.mulr1n //.
  rewrite expn_gt0 //.
  auto with arith.
Qed.

Lemma andB_mask1:
  forall n (bs: BITS n),
    andB bs #1 = (if getBit bs 0 then #1 else #0).
Proof.
  case=> [bs|n /tupleP [b bs]].
  - (* Case: n ~ 0 *)
    by rewrite [bs]tuple0 tuple0.

  - (* Case: n ~ n.+1 *)
    rewrite /andB liftBinOpCons -/andB /= Bool.andb_true_r !fromNat0.
    have ->: andB bs (zero n) = (zero n)
      by apply lift_right_zero; apply andbF.
    have ->: getBit [tuple of b :: bs] 0 = b
      by [].
    case: b.
    + (* Case: b ~ true *)
      by rewrite -incB_fromNat /= tuple.beheadCons fromNat0.

    + (* Case: b ~ false *)
      by rewrite zero_decomp.
Qed.

Lemma orB_invB:
  forall n (bs: BITS n),
    orB bs (invB bs) = ones n.
Proof.
  move=> n bs.
  apply allBitsEq=> k le_k.
  rewrite getBit_liftBinOp =>//.
  rewrite getBit_liftUnOp =>//.
  rewrite orbN /getBit nth_nseq le_k //.
Qed.

Lemma andB_invB:
  forall n (bs: BITS n),
    andB bs (invB bs) = zero n.
Proof.
  move=> n bs.
  apply allBitsEq.
  move=> k le_k.
  rewrite getBit_liftBinOp =>//.
  rewrite getBit_liftUnOp =>//.
  rewrite andbN -fromNat0 getBit_zero //.
Qed.

