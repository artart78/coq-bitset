Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition union n (bs bs' : BITS n) : BITS n := orB bs bs'.

Lemma union_repr n (bs bs' : BITS n) E E' : repr bs E -> repr bs' E' ->
    repr (union bs bs') (E :|: E').
Proof. by move=> -> ->; apply/setP=> i; rewrite !inE getBit_liftBinOp. Qed.
