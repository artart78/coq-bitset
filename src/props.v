From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

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

Lemma getBit_behead:
  forall n (bs: BITS n) b k, k < n ->
    getBit [tuple of b :: bs] k.+1 = getBit bs k.
Proof.
  by compute.
Qed.

Lemma getBit_thead:
  forall n (bs: BITS n) b,
    getBit [tuple of b :: bs] 0 = b.
Proof.
    by compute.
Qed.

Lemma getBit_andB:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    getBit (andB bs bs') k = andb (getBit bs k) (getBit bs' k).
Proof.
  move=> n bs bs' k le_k.
  elim: n k bs bs' le_k=> // n /= IHn k /tupleP[b bs] /tupleP[b' bs'] le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    move=> le_n.
    rewrite !getBit_thead.
    have ->: getBit (andB [tuple of b :: bs] [tuple of b' :: bs']) 0 = andb b b'
      by compute.
    by rewrite //.
  + (* k ~ k + 1 *)
    move=> k IHk le_k.
    rewrite !getBit_behead; last by assumption.
    have ->: getBit (andB [tuple of b :: bs] [tuple of b' :: bs']) k.+1 = getBit (andB bs bs') k
      by compute.
    apply IHn; last by assumption.
    by apply le_k.
Qed.

Lemma getBit_orB:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    getBit (orB bs bs') k = orb (getBit bs k) (getBit bs' k).
Proof.
  move=> n bs bs' k le_k.
  elim: n k bs bs' le_k=> // n /= IHn k /tupleP[b bs] /tupleP[b' bs'] le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    move=> le_n.
    rewrite !getBit_thead.
    have ->: getBit (orB [tuple of b :: bs] [tuple of b' :: bs']) 0 = orb b b'
      by compute.
    by rewrite //.
  + (* k ~ k + 1 *)
    move=> k IHk le_k.
    rewrite !getBit_behead; last by assumption.
    have ->: getBit (orB [tuple of b :: bs] [tuple of b' :: bs']) k.+1 = getBit (orB bs bs') k
      by compute.
    apply IHn; last by assumption.
    by apply le_k.
Qed.

Lemma getBit_xorB:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    getBit (xorB bs bs') k = xorb (getBit bs k) (getBit bs' k).
Proof.
  move=> n bs bs' k le_k.
  elim: n k bs bs' le_k=> // n /= IHn k /tupleP[b bs] /tupleP[b' bs'] le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    move=> le_n.
    rewrite !getBit_thead.
    have ->: getBit (xorB [tuple of b :: bs] [tuple of b' :: bs']) 0 = xorb b b'
      by compute.
    by rewrite //.
  + (* k ~ k + 1 *)
    move=> k IHk le_k.
    rewrite !getBit_behead; last by assumption.
    have ->: getBit (xorB [tuple of b :: bs] [tuple of b' :: bs']) k.+1 = getBit (xorB bs bs') k
      by compute.
    apply IHn; last by assumption.
    apply le_k.
Qed.

Lemma getBit_invB:
  forall n (bs: BITS n) k, k < n -> getBit (invB bs) k = negb (getBit bs k).
Proof.
  move=> n bs k le_k.
  elim: n k bs le_k=> // n /= IHn k /tupleP[b bs] le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    by rewrite //.
  + (* k ~ k + 1 *)
    move=> k IHk le_k.
    rewrite /invB liftUnOpCons -/invB.
    have ->: getBit [tuple of b :: bs] k.+1 = getBit bs k
      by compute.
    have ->: getBit (consB (~~ b) (invB bs)) k.+1 = getBit (invB bs) k
      by compute.
    by apply IHn; apply le_k.
Qed.

Lemma getBit_orB_true:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs k = true -> getBit (orB bs' bs) k = true).
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_orB; last by assumption.
  move ->.
  apply Bool.orb_true_r.
Qed.

Lemma getBit_orB_neg:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs' k = false -> getBit (orB bs bs') k = getBit bs k).
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_orB; last by assumption.
  move ->.
  apply Bool.orb_false_r.
Qed.

Lemma setBit_0:
  forall n, setBit (n := n) #0 0 true = #1.
Proof.
  move=> n.
  elim: n.
  + (* n ~ 0 *)
    by rewrite //.
  + (* n ~ n + 1 *)
    move=> n.
    by rewrite {2}/setBit /setBitAux //= tuple.beheadCons //.
Qed.

Lemma getBit_joinlsb:
  forall n (bs : BITS n) k b, k < n ->
    getBit (joinlsb (bs, b)) k.+1 = getBit bs k.
Proof.
  rewrite //.
Qed.

Lemma getBit_dropmsb:
  forall n (bs : BITS n.+1) k, k < n ->
    getBit (dropmsb bs) k = getBit bs k.
Proof.
  move=> n bs k le_k.
  elim: n k bs le_k=> // n /= IHn k /tupleP[b bs] le_k.
  rewrite /dropmsb /splitmsb /=.
  rewrite tuple.theadCons tuple.beheadCons /=.
  rewrite -/splitmsb.
  have ->: (let (c, r) := splitmsb bs in (c, joinlsb (r, b))).2
    = joinlsb (dropmsb bs, b).
    elim H: splitmsb.
    rewrite /dropmsb //.
    by rewrite H //.
  case: k le_k.
  + (* k ~ 0 *)
    by rewrite //.
  + (* k ~ k + 1 *)
    move=> k le_k.
    rewrite !getBit_joinlsb.
    apply IHn.
    apply le_k.
    auto with arith.
    apply le_k.
Qed.

Lemma dropmsb_joinlsb:
  forall n (bs : BITS n.+1) b,
    dropmsb (joinlsb (bs, b)) = joinlsb (dropmsb bs, b).
Proof.
  move=> n bs b.
  apply allBitsEq.
  move=> k le_k.
  case: k le_k.
  + (* k ~ 0 *)
    rewrite getBit_dropmsb.
    rewrite /joinlsb {2}/getBit.
    rewrite //.
    trivial.
  + (* k ~ k + 1 *)
    move=> k le_k.
    rewrite getBit_dropmsb; last by assumption.
    rewrite getBit_joinlsb; last by auto with arith.
    rewrite getBit_joinlsb; last by assumption.
    rewrite getBit_dropmsb //.
Qed.

Lemma splitlsb_0:
  forall n, splitlsb (n := n) #0 = (#0, false).
Proof.
  move=> n.
  rewrite /splitlsb.
  rewrite /fromNat /=.
  rewrite -/fromNat.
  rewrite tuple.theadCons tuple.beheadCons //.
Qed.

Lemma splitmsb_0:
  forall n, splitmsb (n := n) #0 = (false, #0).
Proof.
  move=> n.
  elim: n=> [|n IHn].
  + (* n ~ 0 *)
    rewrite /splitmsb.
    rewrite splitlsb_0 //.
  + (* n ~ n + 1 *)
    rewrite /splitmsb.
    rewrite //=.
    rewrite tuple.theadCons tuple.beheadCons /=.
    rewrite -/splitmsb.
    rewrite IHn //.
Qed.

Lemma dropmsb_setBit:
  forall n k, k < n ->
    (dropmsb (setBit (n := n.+1) #0 k true) = setBit (n := n) #0 k true).
Proof.
  move=> n k le_k.
  elim: n k le_k=> // n IHn k le_k.
  elim: k le_k=> [|k IHk le_k].
  + (* k ~ 0 *)
    rewrite /=.
    rewrite !tuple.beheadCons /=.
    rewrite dropmsb_joinlsb.
    rewrite /dropmsb.
    rewrite splitmsb_0 //=.
  + (* k ~ k + 1 *)
    rewrite {1}/setBit /setBitAux.
    rewrite -/setBitAux.
    rewrite splitlsb_0.
    rewrite splitlsb_0.
    have ->:
        (match k with
         | 0 => joinlsb (n := n) (# (0), true)
         | i'.+1 => joinlsb (setBitAux i' true # (0), false)
         end) = setBitAux k true #0.
      rewrite {2}/setBitAux //=.
      rewrite tuple.beheadCons tuple.theadCons /=.
      by rewrite -/setBitAux //.
    have ->: setBitAux k true #0 = setBit #0 k true. by trivial.
    rewrite dropmsb_joinlsb.
    rewrite IHn.
    rewrite {2}/setBit /setBitAux.
    rewrite splitlsb_0 //.
    apply le_k.
Qed.

Lemma getBit_shlBn:
  forall n k, k < n -> shlBn (n := n) #1 k = setBit #0 k true.
Proof.
  move=> n k le_k.
  elim: n k le_k=> // n IHn k le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    by rewrite setBit_0 //.
  + (* k ~ k + 1 *)
    move=> k IHk le_k.
    rewrite /shlBn iterS -[iter _ _ _]/(shlBn _ _).
    rewrite IHk.
    rewrite {1}/setBit /setBitAux //=.
    rewrite tuple.beheadCons tuple.theadCons /= -/setBitAux.
    rewrite /shlB /shlBaux.
    rewrite -/setBitAux.
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
    auto with arith.
Qed.

Lemma getBit_shlBn_1:
  forall n k, k < n -> getBit (n := n) (shlBn #1 k) k = true.
Proof.
  move=> n k le_k.
  rewrite getBit_shlBn; last by assumption.
  apply setBitThenGetSame; last by assumption.
Qed.

Lemma getBit_zero:
  forall n k, k < n -> getBit (n := n) #0 k = false.
Proof.
  move=> n k le_k.
  rewrite fromNat0 /zero /copy /getBit nth_nseq le_k //.
Qed.

Lemma getBit_shlBn_0:
  forall n k k', k < n -> k' < n -> k <> k' -> getBit (n := n) (shlBn #1 k) k' = false.
Proof.
  move=> n k k' le_k le_k'.
  rewrite getBit_shlBn; last by assumption.
  have ->: false = getBit (n := n) #0 k'.
  rewrite getBit_zero //.
  apply setBitThenGetDistinct; assumption; assumption.
Qed.

Lemma getBit_settrue:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (orB bs (shlBn #1 k)) x = (if x == k then true else getBit bs x).
Proof.
  move=> n bs k x le_k le_x.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=>H.
    apply getBit_orB_true; first by apply le_x.
    rewrite H.
    by apply getBit_shlBn_1; apply le_k.
  - (* Case: x <> k *)
    move/eqP: H=>H.
    apply getBit_orB_neg; first by apply le_x.
    apply getBit_shlBn_0; first by apply le_k.
    apply le_x.
    by apply not_eq_sym; apply H.
Qed.

Lemma getBit_andB_true:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs' k = true -> getBit (andB bs bs') k = getBit bs k).
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_andB; last by assumption.
  move ->.
  apply Bool.andb_true_r.
Qed.

Lemma getBit_andB_neg:
  forall n (bs: BITS n) (bs': BITS n) k, k < n ->
    getBit bs' k = false -> getBit (andB bs bs') k = false.
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_andB; last by assumption.
  move ->.
  apply Bool.andb_false_r.
Qed.

Lemma getBit_setfalse:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (andB bs (invB (shlBn #1 k))) x = (if x == k then false else getBit bs x).
Proof.
  move=> n bs k x le_k le_x.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=>H.
    apply getBit_andB_neg; first by apply le_x.
    rewrite H getBit_invB; last by apply le_k.
    by rewrite getBit_shlBn_1 //.
  - (* Case: x <> k *)
    move/eqP: H=>H.
    apply getBit_andB_true; first by apply le_x.
    rewrite getBit_invB; last by apply le_x.
    rewrite getBit_shlBn_0 //.
    by apply not_eq_sym; apply H.
Qed.
