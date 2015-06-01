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
  
Lemma getBit_settrue:
  forall n (bs: BITS n) k x, k < n ->
    getBit (orB bs (shlBn #1 k)) x = (if x == k then true else getBit bs x).
Proof.
  admit.
Admitted.

Lemma getBit_setfalse:
  forall n (bs: BITS n) k x, k < n ->
                             getBit (andB bs (invB (shlBn #1 k))) x = (if x == k then false else getBit bs x).
Proof.
  admit.
Admitted.

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
      by apply le_k.
Qed.
