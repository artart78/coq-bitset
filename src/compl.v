From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition compl {n} (bs: BITS n): BITS n
  := invB bs.

Lemma compl_repr:
  forall n (bs: BITS n) k, k < n ->
    getBit (compl bs) k = ~~ (getBit bs k).
Proof.
  move=> n bs k le_k.
  rewrite getBit_inv //.
Qed.
