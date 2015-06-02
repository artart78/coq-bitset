From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition union {n} (bs: BITS n) (bs': BITS n): BITS n
  := orB bs bs'.

Lemma union_repr:
  forall n (bs: BITS n) (bs': BITS n) k, k < n ->
    getBit (union bs bs') k = (getBit bs k) || (getBit bs' k).
Proof.
  admit.
Admitted.
