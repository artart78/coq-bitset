From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.
Require Import props.

Lemma getBit_zero:
  forall n k, k < n -> getBit (n := n) #0 k = false.
Proof.
  move=> n k le_k.
  rewrite fromNat0 /zero /copy /getBit nth_nseq le_k //.
Qed.

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

Lemma getBit_shrBn:
  forall n (bs: BITS n) (k: 'I_n),
    getBit (shrBn bs k) 0 = getBit bs k.
Proof.
  move=> n bs [k le_k].
  elim: n k bs le_k=> // n /= IHn k /tupleP[b bs] le_k.
  (* Case: n ~ n.+1 *)
  case: k le_k => [|k] le_k //.
  (* Case: k ~ k.+1 *)
  have ->: getBit [tuple of b :: bs] k.+1 = getBit bs k
    by compute.
  rewrite shrBn_Sn shrBn_joinmsb0 /joinmsb0 getBit_joinmsb;
    last by apply leq0n.
  by rewrite IHn;
    last by rewrite -ltnS; assumption.
Qed.

Lemma getBit_shlBn:
  forall n k, k < n -> shlBn (n := n) #1 k = setBit #0 k true.
Proof.
  elim=> // n IHn k le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    by rewrite setBit_0.
  + (* k ~ k + 1 *)
    move=> k IHk le_k.
    rewrite /shlBn iterS -[iter _ _ _]/(shlBn _ _).
    rewrite IHk.
    rewrite {1}/setBit /setBitAux //=.
    rewrite tuple.beheadCons tuple.theadCons /= -/setBitAux.
    rewrite /shlB /shlBaux -/setBitAux.
    have ->:
        (match k with
         | 0 => joinlsb (n := n) (# (0), true)
         | i'.+1 => joinlsb (setBitAux i' true # (0), false)
         end) = setBitAux k true #0.
      rewrite {2}/setBitAux //=.
      rewrite tuple.beheadCons tuple.theadCons /=.
      by rewrite -/setBitAux //.
    rewrite -[setBitAux _ _ _]/(setBit _ _ _).
    rewrite dropmsb_joinlsb.
    rewrite dropmsb_setBit //.
    (* TODO: check the ssr doc, but we can extend // with some tactic DB I believe *)
    auto with arith.
Qed.

Lemma getBit_shlBn_true:
  forall n k, k < n -> getBit (n := n) (shlBn #1 k) k = true.
Proof.
  move=> n k le_k.
  rewrite getBit_shlBn; last by assumption.
  apply setBitThenGetSame; last by assumption.
Qed.

Lemma getBit_shlBn_false:
  forall n k k', k < n -> k' < n -> k <> k' ->
                 getBit (n := n) (shlBn #1 k) k' = false.
Proof.
  move=> n k k' ? ?.
  rewrite getBit_shlBn; last by assumption.
  have ->: false = getBit (n := n) #0 k'
    by rewrite getBit_zero.
  apply setBitThenGetDistinct; assumption.
Qed.

Lemma getBit_set_true:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (orB bs (shlBn #1 k)) x = (if x == k then true else getBit bs x).
Proof.
  move=> n bs k x ? ?.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=> ->.
    rewrite getBit_liftBinOp; last by assumption.
    rewrite getBit_shlBn_1; last by assumption.
    by apply orbT.
  - (* Case: x <> k *)
    rewrite getBit_liftBinOp; last by assumption.
    rewrite getBit_shlBn_0; try assumption; last by move/eqP: H; apply: not_eq_sym.
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
    rewrite getBit_liftBinOp; last by assumption.
    rewrite getBit_liftUnOp; last by assumption.
    rewrite getBit_shlBn_1; last by assumption.
    by apply andbF.
  - (* Case: x <> k *)
    rewrite getBit_liftBinOp; last by assumption.
    rewrite getBit_liftUnOp; last by assumption.
    rewrite getBit_shlBn_0; try assumption; last by move/eqP: H; apply not_eq_sym.
    by apply andbT.
Qed.

