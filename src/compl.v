From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition compl {n} (bs: BITS n): BITS n
  := invB bs.

(* TODO: This lemma is not very pleasing: I would expect the
implementation [compl] to be on the left (without [getBit]) and a
high-level spec of the set to be on the right. However, I don't quite
see how to make that happen. It shall become clearer when we write the
spec for the library. *)

Lemma compl_repr:
  forall n (bs: BITS n) k, k < n ->
    getBit (compl bs) k = ~~ (getBit bs k).
Proof.
  move=> n bs k le_k.
  by rewrite getBit_invB.
Qed.
