Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp div ssralg finset.
From Bits
     Require Import bits.
Require Import spec.

Definition create {n} (b: bool): BITS n
  := if b then decB #0 else #0.

Lemma create_repr:
  forall n (b: bool), n > 0 ->
    repr (create b) (if b then [ set : 'I_n ] else set0).
Proof.
  move=> n b gtz_n.
  rewrite /repr -setP /eq_mem=> x.
  rewrite !fun_if !in_set !if_arg.
  rewrite !fromNat0 !decB_zero -!fromNat0 getBit_zero getBit_ones=> //.
  by case: b=> //.
Qed.
