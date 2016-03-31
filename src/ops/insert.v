Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition insert n (bs : BITS n) k: BITS n := orB bs (shlBn #1 k).

Lemma insert_repr n (bs: BITS n) (k: 'I_n) E : repr bs E ->
    repr (insert bs k) (k |: E).
Proof. by move->; apply/setP=> i; rewrite !inE getBit_set_true. Qed.
