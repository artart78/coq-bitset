Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits extraction.axioms32.

Require Import repr_op.

Definition enumNext (x: Int32) :=
  let smallest := land x (neg x) in
  let ripple := add smallest x in
  let ones := lsr (lxor x ripple) (add (toInt 2) (ntz x)) in
  lor ripple ones.

Definition enumNext_set (S: {set 'I_wordsize}) e (H: e \in S) :=
  let s_min := [arg min_(x < e in S) x] in
  let s_next := [arg min_(x < ord0 | ((x \notin S) && [exists y, (y \in S) && (y < x)])) x] in
  [set s_next] :|: [set x in S | x > s_next] :|: [set x in 'I_wordsize | x <= (s_next - s_min - 2)].

Lemma enumNext_correct (x: Int32) (S: {set 'I_wordsize}) e (H: e \in S) :
  machine_repr x S -> machine_repr (enumNext x) (enumNext_set S e H).
Proof.
move=> Hx.
apply union_repr.
admit.
admit.
Admitted.

Cd "examples/enum_parts".

Require Import ExtrOcamlBasic.

Extraction "enum_parts.ml" enumNext.

Cd "../..".
