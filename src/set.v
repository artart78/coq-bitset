From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition set {n}(bs: BITS n) k (b: bool): BITS n
  := if b then orB bs (shlBn #1 k) else andB bs (invB (shlBn #1 k)).

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

Lemma getBit_shlBn_1:
  forall n k, k < n -> getBit (n:=n) (shlBn #1 k) k = true.
Proof.
  move=> n k le_k.
  elim: k le_k.
  + (* k ~ 0 *)
    rewrite //=.
    admit.
  + (* k ~ k + 1 *)
    move=> k H le_k.
    rewrite /shlBn iterS.
    rewrite -[iter _ _ _]/(shlBn _ _).
    admit.
Admitted.

Lemma getBit_shlBn_0:
  forall n k k', k < n -> k' < n -> k <> k' -> getBit (n := n) (shlBn #1 k) k' = false.
Proof.
  admit.
Admitted.

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

Lemma set_repr:
  forall n (bs: BITS n) (k: nat) (b: bool), k < n ->
    set bs k b = setBit bs k b.
Proof.
  move=> n bs k b le_k.
  case: b.
  - (* Case: b ~ true *)
    apply allBitsEq =>[i le_i].
    rewrite /set getBit_settrue.
    case H: (i == k).
    + (* Case: i == k *)
      move/eqP: H=>H.
      by rewrite H setBitThenGetSame //.
    + (* Case: i <> k *)
      move/eqP: H=>H.
      rewrite setBitThenGetDistinct //.
      apply not_eq_sym.
      apply H.
      by apply le_k.
  - (* Case: b ~ false *)
    apply le_i.
    apply allBitsEq =>[i le_i].
    rewrite /set getBit_setfalse.
    case H: (i == k).
    + (* Case: i == k *)
      move/eqP: H=>H.
      by rewrite H setBitThenGetSame //.
    + (* Case: i <> k *)
      move/eqP: H=>H.
      rewrite setBitThenGetDistinct //.
      apply not_eq_sym.
      apply H.
      apply le_k.
      by apply le_i.
Qed.
