Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits extraction.axioms32.

Require Import repr_op.

Definition enumNext (x: Int32) := (* 111001100 *)
  let smallest := keep_min x in(* 000000100 *)
  let ripple := add smallest x in  (* 111010000 *)
  let ones := lsr (lxor x ripple) (add (toInt 2) (ntz x)) in
  lor ripple ones.

Definition set_next (S: {set 'I_wordsize}) := [arg min_(x < ord0 | ((x \notin S) && [exists y, (y \in S) && (y < x)])) x].

Definition set_min (S: {set 'I_wordsize}) e := [arg min_(x < e in S) x].

Definition enumNext_set (S: {set 'I_wordsize}) e (H: e \in S) :=
  let s_min := set_min S e in
  let s_next := set_next S in
  [set s_next] :|: [set x in S | x > s_next] :|: [set x in 'I_wordsize | x <= (s_next - s_min - 2)].

Lemma srn_repr:
  forall i E s, machine_repr i E ->
    machine_repr (lsr i (toInt s)) [set i : 'I_wordsize | i < wordsize - s & @inord wordsize.-1 (i + s) \in E].
Proof.
Admitted.

Lemma enumNext_correct (x: Int32) (S: {set 'I_wordsize}) e (H: e \in S) :
  set_next S <> ord0 ->
  machine_repr x S -> machine_repr (enumNext x) (enumNext_set S e H).
Proof.
move=> Hnext Hx.
have repr_ripple: machine_repr (add (keep_min x) x)
     (set_next S |: [set x0 in S | set_next S < x0]).
  by admit.
apply union_repr=> //.
have ->: add (toInt 2) (ntz x) = toInt (2 + set_min S e).
  by admit.
have ->: [set x0 in 'I_wordsize | x0 <= set_next S - set_min S e - 2] =
[set i : 'I_wordsize | i < wordsize - (2 + set_min S e) & @inord wordsize.-1 (i + (2 + set_min S e)) \in ([set set_next S] :|: [set x in S | x < set_next S])].
  apply/setP=> i; rewrite !inE.
  rewrite andbC andbT.
  rewrite [in _ || (_ && _)]andb_idl.
  rewrite -leq_eqVlt.
  admit.
  admit.
apply srn_repr.
set E' := (set_next S |: [set x0 in S | set_next S < x0]).
have ->: (set_next S |: [set x0 in S | x0 < set_next S]) = (S :\: E') :|: (E' :\: S).
  apply/setP=> i; rewrite !inE.
  rewrite negb_or negb_and.
  rewrite andb_orr.
  rewrite andb_orl.
  rewrite -andbA.
  rewrite andNb andbF.
  symmetry.
  rewrite -orbA orbC orbF.
  rewrite andb_orr.
  rewrite orbA.
  rewrite andbA.
  rewrite andNb orbF.
  rewrite -leqNgt.
  rewrite -ltn_neqAle.
  rewrite orbC.
  rewrite andb_idl.
  by rewrite andbC.
  move: Hnext.
  rewrite /set_next /arg_min.
  case: pickP=> [y //= Ha _ /eqP->|//].
  by move/andP: Ha => [/andP [-> _] _].
apply symdiff_repr=> //.
Admitted.

Cd "examples/enum_parts".

Require Import ExtrOcamlBasic.

Extraction "enum_parts.ml" enumNext.

Cd "../..".
