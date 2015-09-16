From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.

(* TODO: It seems that some lemma here have nothing to do with
[getBit]. Find them and move them to a suitable location. It is very
tempting to merge every files in this directory in a single
[properties.v] file. *)

(** * Commutation properties between [getBit] and various operations *)

(** ** [zero] *)

Lemma getBit_zero:
  forall n k, getBit (n := n) #0 k = false.
Proof.
  move=> n k.
  rewrite fromNat0 /zero /copy /getBit nth_nseq if_same //.
Qed.

(** ** [tcast] *)

Lemma getBit_tcast:
  forall n m (bs: BITS n)(H: n = m), getBit (tcast H bs) = getBit bs.
Proof.
  move=> n m bs H.
  case: m / H.
  rewrite //.
Qed.

(** ** [ones] *)

Lemma getBit_ones:
  forall n k, k < n -> getBit (ones n) k = true.
Proof.
  move=> n k le_k.
  by rewrite /getBit nth_nseq le_k.
Qed.

(** ** [joinmsb] *)

Lemma getBit_joinmsb :
  forall n (bs: BITS n) k,
    k <= n ->
    getBit (joinmsb (false , bs)) k = getBit bs k.
Proof.
  elim=> [|n IHn] bs k leq_k_n.
  - (* Case: n ~ 0 *)
    rewrite leqn0 in leq_k_n.
    move/eqP: leq_k_n=> ->.
    by rewrite !tuple0.
  - (* Case: n ~ n.+1 *)
    case/tupleP: bs=> [b bs].
    case: k leq_k_n => [|k leq_k_n].
    + (* Case: k ~ 0 *)
      by trivial.
    + (* Case: k ~ k.+1 *)
      rewrite /joinmsb/splitlsb tuple.beheadCons
              tuple.theadCons -/joinmsb /joinlsb //=.
      by apply: IHn; assumption.
Qed.


(** ** [dropmsb] *)

Lemma getBit_dropmsb:
  forall n (bs : BITS n.+1) k, k < n ->
    getBit (dropmsb bs) k = getBit bs k.
Proof.
  elim=> // n /= IHn /tupleP[b bs] k le_k.
  rewrite /dropmsb /splitmsb /=
          tuple.theadCons tuple.beheadCons /=
          -/splitmsb.
  set cr := splitmsb bs; rewrite (surjective_pairing cr).
  have ->: ((cr.1, joinlsb (cr.2, b))).2 = joinlsb (dropmsb bs, b)
    by rewrite /dropmsb.
  case: k le_k => // k le_k.
  + (* k ~ k + 1 *)
    have H: forall bs', getBit (joinlsb (bs', b)) k.+1 = getBit bs' k by compute.
    by rewrite !H; auto with arith.
Qed.

(** ** Any binary operation lifted through [liftBinOp] *)

Lemma getBit_liftBinOp:
  forall n op (bs: BITS n)(bs': BITS n) k, k < n ->
    getBit (liftBinOp op bs bs') k = op (getBit bs k) (getBit bs' k).
Proof.
  elim=> // n IHn op /tupleP[b bs] /tupleP[b' bs'];
  case=> [|k] ?.
  + (* k ~ 0 *)
    have ->: getBit (liftBinOp op [tuple of b :: bs] [tuple of b' :: bs']) 0 = op b b'
      by compute.
    by trivial.
  + (* k ~ k + 1 *)
    have ->: getBit [tuple of b :: bs] k.+1 = getBit bs k by compute.
    have ->: getBit [tuple of b' :: bs'] k.+1 = getBit bs' k by compute.
    have ->: getBit (liftBinOp op [tuple of b :: bs] [tuple of b' :: bs']) k.+1 = getBit (liftBinOp op bs bs') k
      by compute.
    by apply IHn.
Qed.

(** ** Any unary operation lifted through [liftUnOp] *)

Lemma getBit_liftUnOp:
  forall n op (bs : BITS n) k, k < n -> getBit (liftUnOp op bs) k = op (getBit bs k).
Proof.
  elim=> // n IHn op /tupleP[b bs];
  case=> // k le_k.
  + (* k ~ k + 1 *)
    rewrite liftUnOpCons.
    have ->: getBit [tuple of b :: bs] k.+1 = getBit bs k
      by compute.
    have ->: getBit (consB (op b) (liftUnOp op bs)) k.+1 = getBit (liftUnOp op bs) k
      by compute.
    by apply IHn; apply le_k.
Qed.

(** ** [shrBn] *)

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

Lemma getBit_shrBn:
  forall n (bs: BITS n) k k', k + k' < n ->
    getBit (shrBn bs k) k' = getBit bs (k + k').
Proof.
  elim=> // n /= IHn /tupleP[b bs] k k' le_kk'.
  (* Case: n ~ n.+1 *)
  case: k le_kk' => [|k] le_kk' //.
  (* Case: k ~ k.+1 *)
  have ->: k.+1 + k' = (k + k').+1 by auto with arith.
  have ->: getBit [tuple of b :: bs] (k + k').+1 = getBit bs (k + k')
    by compute.
  rewrite shrBn_Sn shrBn_joinmsb0 /joinmsb0 getBit_joinmsb;
    last by rewrite (leq_trans (n := k.+1 + k')) // leq_addl //.
  apply IHn; first by auto with arith.
Qed.

(** ** [shlB] and [shlBn] *)

Lemma getBit_shlB:
  forall n (bs: BITS n) k, k > 0 -> k < n ->
    getBit (shlB bs) k = getBit bs k.-1.
Proof.
  move=> n bs k gtz_k ltn_k.
  case: k gtz_k ltn_k=> // k ? ltn_k.
  rewrite /shlB /shlBaux.
  rewrite getBit_dropmsb=> //.
Qed.

Lemma getBit_shlB_0:
  forall n (bs: BITS n), getBit (shlB bs) 0 = false.
Proof.
  elim=> [bs|n Hn /tupleP[b bs]].
  by rewrite tuple0 /getBit.
  by rewrite /shlB /shlBaux getBit_dropmsb.
Qed.

Lemma getBit_shlBn_true:
  forall n k, k < n -> getBit (n := n) (shlBn #1 k) k = true.
Proof.
  elim=> [//|n Hn].
  elim=> [|k Hk] le_k.
  rewrite /shlBn /=.
  rewrite /fromNat //.
  rewrite /shlBn /= getBit_shlB //=.
  rewrite -[iter _ _ _]/(shlBn _ _).
  apply Hk.
  by apply (ltn_trans (n := k.+1)).
Qed.

Lemma getBit_shlBn_false:
  forall n k k', k < n -> k' < n -> k <> k' ->
                 getBit (n := n) (shlBn #1 k) k' = false.
Proof.
  elim=> [//|n Hn].
  elim=> [|k Hk] k' le_k le_k' Hkk'.
  case: k' le_k' Hkk'=> [//|k' le_k' Hkk'].
  rewrite /= /getBit /fromNat /= -/fromNat.
  apply getBit_zero.
  case: k' le_k' Hkk'=> [|k'] le_k' Hkk'.
  rewrite /shlBn /=.
  apply getBit_shlB_0.
  rewrite /shlBn /= -[iter _ _ _]/(shlBn _ _).
  rewrite getBit_shlB /= => //.
  apply Hk.
  apply (ltn_trans (n := k.+1))=> //.
  apply (ltn_trans (n := k'.+1))=> //.
  move/eqP: Hkk'=> Hkk'.
  apply/eqP.
  by rewrite -eqSS.
Qed.

Lemma getBit_shlBn:
  forall n k, k < n -> shlBn (n := n) #1 k = setBit #0 k true.
Proof.
  move=> n k ltn_k.
  apply allBitsEq=> i ltn_i.
  case H: (i == k).
  * move/eqP: H ->.
    rewrite getBit_shlBn_true=> //.
    rewrite setBitThenGetSame=> //.
  * move/eqP: H=> H.
    rewrite getBit_shlBn_false=> //.
    rewrite setBitThenGetDistinct=> //.
    rewrite getBit_zero=> //.
    move=> Habs.
    rewrite Habs in H=> //.
    move=> Habs.
    by rewrite Habs in H.
Qed.

Lemma getBit_set_true:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (orB bs (shlBn #1 k)) x = (if x == k then true else getBit bs x).
Proof.
  move=> n bs k x ? ?.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=> ->.
    rewrite getBit_liftBinOp=> //.
    rewrite getBit_shlBn_true=> //.
    by apply orbT.
  - (* Case: x <> k *)
    rewrite getBit_liftBinOp=> //.
    rewrite getBit_shlBn_false=> //; last by move/eqP: H; apply: not_eq_sym.
    by apply orbF.
Qed.

Lemma getBit_set_false:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (andB bs (invB (shlBn #1 k))) x = (if x == k then false else getBit bs x).
Proof.
  move=> n bs k x ? ?.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=> ->.
    rewrite getBit_liftBinOp=> //.
    rewrite getBit_liftUnOp=> //.
    rewrite getBit_shlBn_true=> //.
    by apply andbF.
  - (* Case: x <> k *)
    rewrite getBit_liftBinOp=> //.
    rewrite getBit_liftUnOp=> //.
    rewrite getBit_shlBn_false=> //; last by move/eqP: H; apply not_eq_sym.
    by apply andbT.
Qed.
