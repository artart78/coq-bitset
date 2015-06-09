From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import Arith.
Require Import props.

Definition set {n}(bs: BITS n) k (b: bool): BITS n
  := if b then orB bs (shlBn #1 k) else andB bs (invB (shlBn #1 k)).

(* TODO(Maxime): should we use "'I_n" or "(k: nat), k < n"? *)
(* TODO(Arthur): give a self-contained example demonstrating our problem with 'I_n. Turn the solution into tutorial. *)

Lemma set_repr:
  forall n (bs: BITS n) (k: nat) (b: bool), k < n ->
    set bs k b = setBit bs k b.
Proof.
  move=> n bs k b le_k.
  apply allBitsEq=> [i le_i].
  case: b.
  - (* Case: b ~ true *)
    rewrite getBit_set_true //.
    (* TODO: write some Ltac to automate this proof pattern. 

       Calling allBitsEq introduce a [getBit] at some index [i]. If
       the inner operation is a [setBit] at some index [k], we want to
       use [setBitThenGetSame] and [setBitThenGetDistinct]. 

       This should remove the proof duplication below.
     *)
    case H: (i == k).
    + (* Case: i == k *)
      move/eqP: H=> ->.
      by rewrite setBitThenGetSame //.
    + (* Case: i <> k *)
      rewrite setBitThenGetDistinct //.
      by move/eqP: H; apply not_eq_sym.
  - (* Case: b ~ false *)
    rewrite getBit_set_false //.
    case H: (i == k).
    + (* Case: i == k *)
      move/eqP: H=> ->.
      by rewrite setBitThenGetSame //.
    + (* Case: i <> k *)
      rewrite setBitThenGetDistinct //.
      by move/eqP: H; apply not_eq_sym.
Qed.
