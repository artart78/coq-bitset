Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp div ssralg finset.
From Bits
     Require Import bits.
Require Import spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition create {n} (b: bool): BITS n := if b then decB #0 else #0.

Lemma create_repr n (b : bool) (n_gt0 : 0 < n) :
    repr (create b) (if b then [set : 'I_n] else set0).
Proof.
apply/setP=> i; rewrite !inE !fun_if !if_arg.
rewrite fromNat0 decB_zero -fromNat0 getBit_zero getBit_ones //.
by case: b; rewrite inE.
Qed.
