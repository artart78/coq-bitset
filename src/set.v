From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import Arith.
Require Import specs props.

Definition set {n}(bs: BITS n) k (b: bool): BITS n
  := if b then orB bs (shlBn #1 k) else andB bs (invB (shlBn #1 k)).

Lemma set_repr:
  forall n (bs: BITS n) (k: nat) (b: bool), k < n ->
    set bs k b = setBit bs k b.
Proof.
  move=> n bs k b le_k.
  case: b.
  - (* Case: b ~ true *)
    apply allBitsEq =>[i le_i].
    rewrite /set getBit_settrue; last by assumption.
    case H: (i == k).
    + (* Case: i == k *)
      move/eqP: H=>H.
      by rewrite H setBitThenGetSame //.
    + (* Case: i <> k *)
      move/eqP: H=>H.
      rewrite setBitThenGetDistinct //.
      by apply not_eq_sym; apply H.
    by apply le_k.
  - (* Case: b ~ false *)
    apply allBitsEq =>[i le_i].
    rewrite /set getBit_setfalse; last by assumption.
    case H: (i == k).
    + (* Case: i == k *)
      move/eqP: H=>H.
      by rewrite H setBitThenGetSame //.
    + (* Case: i <> k *)
      move/eqP: H=>H.
      rewrite setBitThenGetDistinct //.
      by apply not_eq_sym; apply H.
    by apply le_k.
Qed.
