From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition create {n} (b: bool): BITS n
  := if b then (subB (shlBn #1 n) #1) else #0.

Lemma create_repr:
  forall n (b: bool),
    create b = if b then ones n else zero n.
Proof.
  admit.
Admitted.
