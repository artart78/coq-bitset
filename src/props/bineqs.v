From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From MathComp
     Require Import tuple zmodp div ssralg.
From Bits
     Require Import bits.
Require Import getbit.

(* TODO: what is this file about? 
         combinatorial of boolean operations? *)

Lemma toNat_andB:
  forall n (bs: BITS n) bs', toNat (andB bs bs') <= toNat bs'.
Proof.
  elim=> [bs bs'|n IH /tupleP[b bs] /tupleP[b' bs']].
  + by rewrite tuple0.
  + rewrite /andB liftBinOpCons -/andB /=.
    rewrite /toNat /consB /=.
    apply leq_add.
    elim: b=> //.
    rewrite leq_double.
    by apply IH.
Qed.

Lemma count_ones:
  forall n, (count_mem true (ones n)) = n.
Proof.
  elim=> //=.
  auto with arith.
Qed.



(* TODO: there are 3 lemmas similar to this. Are they really needed? *)

Lemma nat_cast_ord:
  forall n m (H: n = m) (i: 'I_n), nat_of_ord (cast_ord H i) = i.
Proof.
  move=> n m H i.
  by case: m / H.
Qed.

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
    rewrite /shlBn iterS -[iter _ _ _]/(shlBn _ _) getBit_shlB=> //.
    rewrite getBit_shlBn_false=> //.
    apply/eqP.
    rewrite gtn_eqF //.
    by rewrite -(ltn_add2r 1) !addn1 prednK.
  + (* k <= 0 *)
    have ->: k = 0.
      by case: k le_k k_gtz=> //.
    by rewrite /shlBn iterS -[iter _ _ _]/(shlBn _ _) getBit_dropmsb=> //.
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
      have: true = false=> //.
      have->: true = getBit (n := n) (shlBn #1 k) k by rewrite getBit_shlBn_true.
      have->: false = getBit (n := n) #0 k by rewrite getBit_zero.
      by rewrite k_neqz //.
    + (* k >= n *)
      have ->: k = n=> //.
        apply/eqP.
        by rewrite -[k == n]orbF -ltn_k -leq_eqVlt.
  + (* shlBn #1 k <> #0 -> k < n *)
    rewrite toNat_shlBn //.
    case k_eq_n: (k == n).
    + (* k == n *)
      move/eqP: k_neqz=>k_neqz.
      exfalso.
      apply k_neqz.
      move/eqP: k_eq_n ->.
      by apply shlBn_overflow.
    + (* k <> n *)
      by rewrite ltn_neqAle k_eq_n le_k.
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
  by rewrite orbN /getBit nth_nseq le_k.
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
  by rewrite andbN -fromNat0 getBit_zero.
Qed.

Lemma leB_andB:
  forall n (bs: BITS n) (bs': BITS n), leB (andB bs bs') bs'.
Proof.
  elim=> [bs bs'|n IHn /tupleP[b bs] /tupleP[b' bs']].
  + (* n ~ 0 *)
    by rewrite !tuple0 [bs']tuple0.
  + (* n ~ n.+1 *)
    rewrite /andB liftBinOpCons -/andB /leB /ltB /=
            !tuple.beheadCons !tuple.theadCons -/ltB.
    case H: (ltB (andB bs bs') bs').
      by rewrite /leB in IHn.
    have H': (andB bs bs' == bs').
      rewrite -[andB _ _ == _]orbF orbC -H.
      by apply IHn.
    rewrite H'.
    move/eqP: H'->.
    case: b'=> /=.
    + (* b' = true *)
      rewrite !andbT.
      by case: b=> /=.
    + (* b' = false *)
      by rewrite !andbF orbC orbF //.
Qed.

