Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition remove n (bs : BITS n) k : BITS n := andB bs (invB (shlBn #1 k)).

Lemma remove_repr n (bs : BITS n) (k: 'I_n) E : repr bs E ->
    repr (remove bs k) (E :\ k).
Proof.
move->; apply/setP=> i.
by rewrite !inE getBit_set_false // fun_if !val_eqE; case: eqP.
Qed.
