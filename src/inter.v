From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition inter {n} (bs: BITS n) (bs': BITS n): BITS n
  := andB bs bs'.

Lemma inter_repr:
  forall n (bs: BITS n) (bs': BITS n) k, k < n ->
    getBit (inter bs bs') k = (getBit bs k) && (getBit bs' k).
Proof.
  move=> n bs bs' k le_k.
  rewrite getBit_andB_andb //.
Qed.
