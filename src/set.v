From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition set {n}(bs: BITS n) k (b: bool): BITS n
  := if b then orB bs (shlBn #1 k) else andB bs (invB (shlBn #1 k)).

Lemma getBit_id:
  forall n (bs1: BITS n) (bs2: BITS n),
    (forall k, k < n -> getBit bs1 k = getBit bs2 k) -> bs1 = bs2.
Proof.
  move=> n bs1 bs2.
  move=> H.
  apply eq_from_tnth.
  rewrite /eqfun =>x.
  rewrite /getBit in H.
  rewrite !(tnth_nth false).
  move: x=>[x le_x].
  apply H.
  apply le_x.
Qed.

Lemma getBit_orB_left:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs k = true -> getBit (orB bs bs') k = true).
Proof.
  admit.
Admitted.

Lemma getBit_orB_right:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs k = true -> getBit (orB bs' bs) k = true).
Proof.
  admit.
Admitted.

Lemma getBit_orB_neg_left:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs k = false -> getBit (orB bs bs') k = getBit bs' k).
Proof.
  admit.
Admitted.

Lemma getBit_orB_neg_right:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs' k = false -> getBit (orB bs bs') k = getBit bs k).
Proof.
  admit.
Admitted.

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
    apply getBit_orB_right.
    apply le_x.
    rewrite H.
    apply getBit_shlBn_1.
    apply le_k.
  - (* Case: x <> k *)
    move/eqP: H=>H.
    apply getBit_orB_neg_right.
    apply le_x.
    apply getBit_shlBn_0.
    apply le_k.
    apply le_x.
    apply not_eq_sym.
    apply H.
Qed.

Lemma getBit_andB_left:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs k = true -> getBit (andB bs bs') k = getBit bs' k).
Proof.
  admit.
Admitted.

Lemma getBit_andB_right:
  forall n (bs: BITS n)(bs': BITS n) k, k < n ->
    (getBit bs' k = true -> getBit (andB bs bs') k = getBit bs k).
Proof.
  admit.
Admitted.

Lemma getBit_andB_neg_right:
  forall n (bs: BITS n) (bs': BITS n) k, k < n ->
    getBit bs' k = false -> getBit (andB bs bs') k = false.
Proof.
  admit.
Admitted.

Lemma getBit_inv_shlBn_0:
  forall n k, k < n -> getBit (n := n) (invB (shlBn #1 k)) k = false.
Proof.
  admit.
Admitted.

Lemma getBit_inv_shlBn_1:
  forall n k k', k < n -> k' < n -> k <> k' -> getBit (n := n) (invB (shlBn #1 k)) k' = true.
Proof.
  admit.
Admitted.

Lemma getBit_setfalse:
  forall n (bs: BITS n) k x, k < n -> x < n ->
    getBit (andB bs (invB (shlBn #1 k))) x = (if x == k then false else getBit bs x).
Proof.
  move=> n bs k x le_k le_x.
  case H: (x == k).
  - (* Case: x == k *)
    move/eqP: H=>H.
    apply getBit_andB_neg_right.
    apply le_x.
    by rewrite H getBit_inv_shlBn_0 //.
  - (* Case: x <> k *)
    move/eqP: H=>H.
    apply getBit_andB_right.
    apply le_x.
    rewrite getBit_inv_shlBn_1 //.
    by apply not_eq_sym; apply H.
Qed.

Lemma set_repr:
  forall n (bs: BITS n) (k: nat) (b: bool), k < n ->
    set bs k b = setBit bs k b.
Proof.
  move=> n bs k b le_k.
  case: b.
  - (* Case: b ~ true *)
    apply getBit_id =>[i le_i].
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
    apply getBit_id =>[i le_i].
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
