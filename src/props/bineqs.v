From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.
Require Import props.

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

Lemma shrB_joinmsb0:
  forall n (bs: BITS n),
    shrB (joinmsb0 bs) = joinmsb0 (shrB bs).
Proof.
  case=> [bs|n /tupleP [b bs]].
  - (* Case: n ~ 0 *)
    by rewrite tuple0.
  - (* Case: n ~ n.+1 *)
    rewrite /shrB; apply f_equal.
    have ->: droplsb [tuple of b :: bs] = bs
      by rewrite /droplsb/splitlsb //= tuple.beheadCons.
    have ->: joinmsb0 [tuple of b :: bs] = [tuple of b :: joinmsb0 bs]
      by rewrite /joinmsb0 //= tuple.theadCons tuple.beheadCons.
    by rewrite /droplsb //= tuple.beheadCons.
Qed.

Lemma shrBn_joinmsb0:
  forall n (bs: BITS n) k,
    shrBn (joinmsb0 bs) k = joinmsb0 (shrBn bs k).
Proof.
  move=> n bs.
  elim=> [|k IHk].
  - (* Case: k ~ 0 *)
    by trivial.
  - (* Case: k ~ k.+1 *)
    rewrite {1}/shrBn iterS -[iter _ _ _]/(shrBn _ _).
    by rewrite -shrB_joinmsb0 IHk.
Qed.

Lemma shrBn_Sn :
  forall n b (bs: BITS n) k,
    shrBn [tuple of b :: bs] k.+1 = shrBn (joinmsb0 bs) k.
Proof.
  move=> n b S k.
  by rewrite {1}/shrBn iterSr //= /droplsb //= tuple.beheadCons.
Qed.

Lemma dropmsb_joinlsb:
  forall n (bs : BITS n.+1) b,
    dropmsb (joinlsb (bs, b)) = joinlsb (dropmsb bs, b).
Proof.
  move=> n bs b.
  apply allBitsEq.
  case=> [|k] ?.
  + (* k ~ 0 *)
    by rewrite getBit_dropmsb /joinlsb/getBit.
  + (* k ~ k + 1 *)
    rewrite getBit_dropmsb; last by assumption.
    have H: forall bs', getBit (joinlsb (bs', b)) k.+1 = getBit bs' k by compute.
    by rewrite !H getBit_dropmsb.
Qed.

Lemma splitlsb_0:
  forall n, splitlsb (n := n) #0 = (#0, false).
Proof.
  move=> n.
  by rewrite /splitlsb 
             /fromNat /= -/fromNat
             tuple.theadCons tuple.beheadCons.
Qed.

Lemma splitmsb_0:
  forall n, splitmsb (n := n) #0 = (false, #0).
Proof.
  elim=> [|n IHn].
  + (* n ~ 0 *)
    by rewrite /splitmsb splitlsb_0.
  + (* n ~ n + 1 *)
    by rewrite /splitmsb /= 
               tuple.theadCons tuple.beheadCons -/splitmsb 
               IHn.
Qed.

Lemma orB_invB:
  forall n (bs: BITS n),
    orB bs (invB bs) = ones n.
Proof.
  move=> n bs.
  apply allBitsEq=> k le_k.
  rewrite getBit_liftBinOp; last by assumption.
  rewrite getBit_liftUnOp; last by assumption.
  rewrite orbN /getBit nth_nseq le_k //.
Qed.

Lemma andB_invB:
  forall n (bs: BITS n),
    andB bs (invB bs) = zero n.
Proof.
  move=> n bs.
  apply allBitsEq.
  move=> k le_k.
  rewrite getBit_liftBinOp; last by assumption.
  rewrite getBit_liftUnOp; last by assumption.
  rewrite andbN -fromNat0 getBit_zero //.
Qed.

