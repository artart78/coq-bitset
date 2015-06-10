From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import props.getbit.

Definition symdiff {n} (bs: BITS n) (bs': BITS n): BITS n
  := xorB bs bs'.

Lemma symdiff_repr:
  forall n (bs: BITS n) (bs': BITS n) k, k < n ->
    getBit (symdiff bs bs') k = xorb (getBit bs k) (getBit bs' k).
Proof.
  move=> n bs bs' k le_k.
  by rewrite getBit_liftBinOp.
Qed.
