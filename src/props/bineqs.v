From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.
Require Import tozp getbit.

(* TODO: merge makeOnes & makeOnes2? *)
Lemma makeOnes:
  forall n,
    ones n = decB #0.
Proof.
  move=> n.
  apply toNat_inj.
  rewrite toNat_ones toNat_decB.
  by have ->: fromNat (n := n) 0 == #0 by apply/eqP.
Qed.

Lemma toNat_tcast:
  forall n m (bs: BITS n)(H: n = m), toNat (tcast H bs) = toNat bs.
Proof.
  move=> n m bs H.
  by case: m / H.
Qed.

Lemma shlBn_overflow:
  forall n, shlBn (n := n) #1 n = #0.
Proof.
  move=> n.
  apply allBitsEq.
  elim: n=> [//|n IHn] k le_k.
  rewrite getBit_zero.
  case k_gtz: (k > 0).
  + (* k > 0 *)
    have predk_lt_k: k.-1 < k.
      by rewrite -(ltn_add2r 1) !addn1 prednK //.
    have predk_lt_Sn: k.-1 < n.+1.
      by rewrite (ltn_trans (n := k))=> //.
    rewrite /shlBn iterS.
    rewrite -[iter _ _ _]/(shlBn _ _).
    rewrite getBit_shlB=> //.
    rewrite getBit_shlBn_false=> //.
    apply/eqP.
    rewrite gtn_eqF //.
    rewrite -(ltn_add2r 1).
    rewrite !addn1.
    rewrite prednK //.
  + (* k <= 0 *)
    have ->: k = 0.
      by case: k le_k k_gtz=> //.
    rewrite /shlBn iterS -[iter _ _ _]/(shlBn _ _).
    rewrite /shlB /shlBaux.
    rewrite getBit_dropmsb=> //.
Qed.

Lemma makeOnes2:
  forall n k (q: k + (n - k) = n), k <= n -> decB (shlBn #1 k) = tcast q (zero (n - k) ## ones k).
Proof.
  move=> n k q le_k.
  apply toNat_inj.
  rewrite toNat_tcast toNat_decB toNatCat toNat_zero mul0n add0n.
  rewrite toNat_ones.
  case k_neqz: (shlBn #1 k == #0).
  + (* shlBn #1 k == #0 -> k >= n *)
    case ltn_k: (k < n).
    + (* k < n *)
      move/eqP: k_neqz=>k_neqz.
      exfalso.
      have: true = false=> //.
      have->: true = getBit (n := n) (shlBn #1 k) k by rewrite getBit_shlBn_true.
      have->: false = getBit (n := n) #0 k by rewrite getBit_zero.
      by rewrite k_neqz //.
    + (* k >= n *)
      have ->: k = n=> //.
        apply/eqP.
        rewrite -[k == n]orbF.
        rewrite -ltn_k.
        by rewrite -leq_eqVlt //.
  + (* shlBn #1 k <> #0 -> k < n *)
    rewrite toNat_shlBn //.
    case k_eq_n: (k == n).
    + (* k == n *)
      move/eqP: k_neqz=>k_neqz.
      exfalso.
      apply k_neqz.
      move/eqP: k_eq_n=>k_eq_n.
      rewrite k_eq_n.
      by apply shlBn_overflow.
    + (* k <> n *)
      rewrite ltn_neqAle.
      by rewrite k_eq_n le_k //.
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

Lemma leB_andB:
  forall n (bs: BITS n) (bs': BITS n), leB (andB bs bs') bs'.
Proof.
  elim=> [bs bs'|n IHn /tupleP[b bs] /tupleP[b' bs']].
  + (* n ~ 0 *)
    by rewrite !tuple0 [bs']tuple0.
  + (* n ~ n.+1 *)
    rewrite /andB liftBinOpCons -/andB.
    rewrite /leB.
    rewrite /ltB.
    rewrite /= !tuple.beheadCons !tuple.theadCons.
    rewrite -/ltB.
    case H: (ltB (andB bs bs') bs').
      rewrite //.
      rewrite /leB in IHn.
    have H': (andB bs bs' == bs').
      rewrite -[andB _ _ == _]orbF.
      rewrite orbC.
      rewrite -H.
      by apply IHn.
    rewrite H'.
    move/eqP: H'->.
    rewrite /=.
    case: b'=> /=.
      rewrite !andbT.
      case: b => //=.
      rewrite !andbF.
      rewrite orbC orbF //.
Qed.

