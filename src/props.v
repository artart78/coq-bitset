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

Lemma getBit_orB_orb:
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
    rewrite !getBit_behead.
    have ->: getBit (orB [tuple of b :: bs] [tuple of b' :: bs']) k.+1 = getBit (orB bs bs') k
      by compute.
    apply IHn.
    apply le_k.
    apply le_k.
    apply le_k.
Qed.

Lemma getBit_orB_true:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs k = true -> getBit (orB bs' bs) k = true).
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_orB_orb.
  move ->.
  apply Bool.orb_true_r.
  apply le_k.
Qed.

Lemma getBit_orB_neg:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs' k = false -> getBit (orB bs bs') k = getBit bs k).
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_orB_orb.
  move ->.
  apply Bool.orb_false_r.
  apply le_k.
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

Lemma setBit_true:
  forall n k, k < n -> setBit (n := n.+1) #0 k true = joinmsb (false, setBit (n := n) #0 k true).
Proof.
  admit.
Admitted.

Lemma getBit_shlBn:
  forall n k, k < n -> shlBn (n := n) #1 k = setBit #0 k true.
Proof.
  move=> n k le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    by rewrite /= setBit_0 //.
  + (* k ~ k + 1 *)
    move=> k IHk le_k.
    rewrite /shlBn iterS -[iter _ _ _]/(shlBn _ _).
    rewrite IHk.
    rewrite /shlB.
    rewrite /shlBaux.
    admit.
    auto with arith.
Admitted.

Lemma getBit_shlBn_1:
  forall n k, k < n -> getBit (n := n) (shlBn #1 k) k = true.
Proof.
  move=> n k le_k.
  rewrite getBit_shlBn.
  apply setBitThenGetSame.
  apply le_k.
  apply le_k.
Qed.

Lemma getBit_zero:
  forall n k, k < n -> getBit (n := n) #0 k = false.
Proof.
  move=> n k le_k.
  rewrite fromNat0.
  rewrite /zero.
  rewrite /copy /getBit.
  rewrite nth_nseq.
  rewrite le_k //.
Qed.

Lemma getBit_shlBn_0:
  forall n k k', k < n -> k' < n -> k <> k' -> getBit (n := n) (shlBn #1 k) k' = false.
Proof.
  move=> n k k' le_k le_k'.
  rewrite getBit_shlBn.
  have ->: false = getBit (n := n) #0 k'.
  rewrite getBit_zero //.
  apply setBitThenGetDistinct.
  apply le_k.
  apply le_k'.
  apply le_k.
Qed.

Lemma getBit_settrue:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (orB bs (shlBn #1 k)) x = (if x == k then true else getBit bs x).
Proof.
  move=> n bs k x le_k le_x.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=>H.
    apply getBit_orB_true.
    apply le_x.
    rewrite H.
    apply getBit_shlBn_1.
    apply le_k.
  - (* Case: x <> k *)
    move/eqP: H=>H.
    apply getBit_orB_neg.
    apply le_x.
    apply getBit_shlBn_0.
    apply le_k.
    apply le_x.
    apply not_eq_sym.
    apply H.
Qed.

Lemma getBit_andB_andb:
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
    rewrite !getBit_behead.
    have ->: getBit (andB [tuple of b :: bs] [tuple of b' :: bs']) k.+1 = getBit (andB bs bs') k
      by compute.
    apply IHn.
    apply le_k.
    apply le_k.
    apply le_k.
Qed.

Lemma getBit_andB_true:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs' k = true -> getBit (andB bs bs') k = getBit bs k).
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_andB_andb.
  move ->.
  apply Bool.andb_true_r.
  apply le_k.
Qed.

Lemma getBit_andB_neg:
  forall n (bs: BITS n) (bs': BITS n) k, k < n ->
    getBit bs' k = false -> getBit (andB bs bs') k = false.
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_andB_andb.
  move ->.
  apply Bool.andb_false_r.
  apply le_k.
Qed.

Lemma getBit_inv:
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
    apply IHn.
    apply le_k.
Qed.

Lemma getBit_setfalse:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (andB bs (invB (shlBn #1 k))) x = (if x == k then false else getBit bs x).
Proof.
  move=> n bs k x le_k le_x.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=>H.
    apply getBit_andB_neg.
    apply le_x.
    rewrite H getBit_inv.
    rewrite getBit_shlBn_1 //.
    by apply le_k.
  - (* Case: x <> k *)
    move/eqP: H=>H.
    apply getBit_andB_true.
    apply le_x.
    rewrite getBit_inv.
    rewrite getBit_shlBn_0 //.
    apply not_eq_sym; apply H.
    by apply le_x.
Qed.

