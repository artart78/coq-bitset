Require Import FMapList OrderedType OrderedTypeEx Compare_dec Peano_dec.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset div.
From CoqEAL Require Import refinements hrel.
From Bits
     Require Import bits ops extraction.axioms32.
Require Import ops spec.

(*Require keep_min min cardinal shift.*)

Import Refinements.Op.
Import Logical.Op.

Local Open Scope rel_scope.

(** * A formalisation of bitsets using OCaml's integers *)

(** 
    
    We establish a relation between OCaml's types (which extracts
    efficiently to machine-native datatypes) and the finset
    library. This is achieved by composing the representation of [BITS
    32] with OCaml's [int] (defined in [coq:bits]) and the
    representation of [finset] with [BITS n].

 *)


From Bits 
     Require Import axioms32.

Global Instance get_Rnative: 
  refines (Rnative ==> Rnative ==> param.bool_R)%rel get get.
Proof. param (get_R (Bits_R := Rnative)). Qed.

Global Instance singleton_Rnative: 
  refines (Rnative ==> Rnative)%rel singleton singleton.
Proof. param singleton_R. Qed.

Global Instance compl_Rnative: 
  refines (Rnative ==> Rnative)%rel compl compl.
Proof. param compl_R. Qed.

Global Instance create_Rnative: 
  refines (param.bool_R ==> Rnative)%rel create create.
Proof. param create_R. Qed.

Global Instance inter_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel inter inter.
Proof. param inter_R. Qed.

Global Instance union_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel union union.
Proof. param union_R. Qed.

Global Instance min_Rnative: 
  refines (Rnative ==> Rnative)%rel min min.
Proof. param min_R. Qed.

Global Instance insert_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel insert insert.
Proof. param insert_R. Qed.

Global Instance remove_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel remove remove.
Proof. param remove_R. Qed.

Global Instance symdiff_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel symdiff symdiff.
Proof. param symdiff_R. Qed.

Global Instance subset_Rnative: 
  refines (Rnative ==> Rnative ==> param.bool_R)%rel subset subset.
Proof. param (subset_R (Bits_R := Rnative)). Qed.




Definition Rmachine: Int32 -> {set 'I_wordsize} -> Type 
  := Rnative \o (@Rfin wordsize).

Definition Rord : Int32 -> 'I_wordsize -> Type
  := Rnative \o Rord.


Global Instance eq_Rmachine: 
  refines (Rmachine ==> Rmachine ==> param.bool_R) eq eq_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance zero_Rmachine: 
  refines Rmachine 0%C empty_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance singleton_repr:
  refines (Rord ==> Rmachine) singleton singleton_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance compl_Rmachine: 
  refines (Rmachine ==> Rmachine) ~%C compl_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance empty_Rmachine:
  refines Rmachine 0%C empty_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance full_Rmachine:
  refines Rmachine (0 - 1)%C full_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance get_Rmachine:
  refines (Rord ==> Rmachine ==> param.bool_R) get get_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance inter_Rmachine:
  refines (Rmachine ==> Rmachine ==> Rmachine) inter inter_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance union_Rmachine:
  refines (Rmachine ==> Rmachine ==> Rmachine) union union_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance insert_Rmachine:
  refines (Rord ==> Rmachine ==> Rmachine) insert set_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance remove_Rmachine:
  refines (Rmachine ==> Rord ==> Rmachine) remove remove_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance symdiff_Rmachine:
  refines (Rmachine ==> Rmachine ==> Rmachine) symdiff symdiff_op.
Proof. eapply refines_trans; tc. Qed.

Global Instance subset_Rmachine:
  refines (Rmachine ==> Rmachine ==> param.bool_R) subset subset_op.
Proof. eapply refines_trans; tc. Qed.

Lemma min_Rmachine:
  forall i E x, Rmachine i E -> x \in E ->
    Rmachine (spec.min i) [set [arg min_(k < x in E) k]].
Admitted.
(*
Proof.
  move=> i E x H Hx.
  move: H=> [bv [Hbv1 Hbv2]].
  exists (keep_min.keep_min bv).
  split.
  apply land_repr=> //.
  apply neg_repr=> //.
  by apply keep_min.keep_min_repr.
Qed.
*)


(** ** Left & right shift *)

Lemma sl_repr:
  forall i E, Rmachine i E ->
    Rmachine (lsl i one) [set i : 'I_wordsize | 0 < i & @inord wordsize.-1 i.-1 \in E].
Admitted.
(*
Proof.
  move=> i E [bv [r_native r_set]].
  exists (shlBn bv 1); split.
  * apply: lsl_repr=> //.
    apply/existsP; eexists; apply/andP; split; first by apply one_repr.
    done.
  * have H: wordsize = wordsize.-1.+1 by compute.
    have ->: [set i0 : 'I_wordsize | 0 < i0 & inord i0.-1 \in E]
           = [set i0 : 'I_wordsize | 0 < i0 & cast_ord H (inord i0.-1) \in E].
      rewrite -setP /eq_mem=> x.
      rewrite !in_set.
      have ->: cast_ord H (inord x.-1) = inord x.-1.
        apply ord_inj.
        by rewrite nat_cast_ord.
      by rewrite //.
    by apply shift.sl_repr.
Qed.
*)

Lemma sr_repr:
  forall i E, Rmachine i E ->
    Rmachine (lsr i one) [set i : 'I_wordsize | i < wordsize.-1 & @inord wordsize.-1 i.+1 \in E].
Admitted.
(*
Proof.
  move=> i E [bv [r_native r_set]].
  exists (shrBn bv 1); split.
  * apply: lsr_repr=> //.
    apply/existsP; eexists; apply/andP; split; first by apply one_repr.
    done.
  * have H: wordsize = wordsize.-1.+1 by compute.
    have ->: [set i0 : 'I_wordsize | i0 < wordsize.-1 & inord i0.+1 \in E]
           = [set i0 : 'I_wordsize | i0 < wordsize.-1 & cast_ord H (inord i0.+1) \in E].
      rewrite -setP /eq_mem=> x.
      rewrite !in_set.
      have ->: cast_ord H (inord x.+1) = inord x.+1.
        apply ord_inj.
        by rewrite nat_cast_ord.
      by rewrite //.
    by apply shift.sr_repr.
Qed.
*)

(** ** Cardinality *)


(* TODO: get rid of this section *)
(** We go from Coq's [nat] to [Int] by (brutally) collapsing [nat]
    to [int]: *)
Extract Inductive nat => int [ "0" "succ" ]
                             "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Axiom toInt: nat -> Int32.

Extract Inlined Constant toInt => "".

Axiom toInt_def : forall n, toInt n = bitsToInt32 (# n).


Axiom fromInt: Int32 -> nat.

Extract Inlined Constant fromInt => "".

Axiom fromInt_def : forall n, fromInt n = toNat (bitsFromInt32 n).


Lemma fromInt_inj: forall x y,
  fromInt x = fromInt y -> x = y.
Admitted.
(*
Proof.
  move=> x y H.
  rewrite !fromInt_def in H.
  apply toNat_inj in H.
  by apply bitsFromInt32_inj in H.
Qed.
*)

(*
Module Int_as_OT <: OrderedType.

  Definition t := Int32.

  Definition eq x y : Prop := (fromInt x) = (fromInt y).

  Definition lt x y : Prop := (fromInt x) < (fromInt y).
  Definition eq_refl x := @Logic.eq_refl nat (fromInt x).
  Definition eq_sym x y := @Logic.eq_sym nat (fromInt x) (fromInt y).
  Definition eq_trans x y z := @Logic.eq_trans nat (fromInt x) (fromInt y) (fromInt z).

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
  move=> x y z H1 H2.
  rewrite /lt.
  apply (ltn_trans (n := fromInt y)).
  apply H1.
  apply H2.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  move=> x y H.
  rewrite /lt in H.
  move=> Habs.
  move/eqP: Habs=> Habs.
  by rewrite ltn_eqF in Habs.
  Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    case_eq (nat_compare (fromInt x) (fromInt y)); intro.
    - apply EQ.
      by apply nat_compare_eq.
    - apply LT.
      apply/ltP.
      by apply nat_compare_Lt_lt.
    - apply GT.
      apply/ltP.
      by apply nat_compare_Gt_gt.
  Qed.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    move=> x y.
    by apply eq_nat_dec.
  Qed.

End Int_as_OT.

Module M := FMapList.Make(Int_as_OT).

Definition tableSize := 4.

Fixpoint pop_tableAux (i: nat) (m: M.t Int32) :=
  match i with
  | 0 => M.add zero zero m
  | i'.+1 => M.add (toInt i) (toInt (count_mem true (fromNat (n := tableSize) i))) (pop_tableAux i' m)
  end.

Definition pop_table := pop_tableAux (2 ^ tableSize) (M.empty Int32).

Definition pop_elem (bs: Int32)(i: nat): Int32
  := let x := land (lsr bs (toInt (i * tableSize))) 
                            (sub (lsl one (toInt tableSize)) 1%C) in
     match (M.find x pop_table) with
     | None => zero
     | Some x => x
     end.

Lemma pop_elem_repr: 
  forall n bs i,
    (i * tableSize <= wordsize)%nat ->
    Rnative n bs ->
    Rnative (pop_elem n i) (cardinal.pop_elem tableSize bs i).
Admitted.
(*
Proof.
  move=> n bs i ? ?.
  rewrite /pop_elem/cardinal.pop_elem.
  rewrite /cardinal.pop_table.
  rewrite nth_mkseq.
  set i' := land (lsr n (toInt (i * tableSize))) ((lsl one (toInt tableSize)) - 1)%C.
  rewrite (M.find_1 (e := toInt (count_mem true (fromNat (n := tableSize) (fromInt i'))))).
  have ->: fromInt i' = toNat (andB (shrBn bs (i * tableSize)) (decB (shlBn # (1) tableSize))).
    rewrite fromInt_def.
    have ->: bitsFromInt32 i' = andB (shrBn bs (i * tableSize)) (decB (shlBn # (1) tableSize)).
      apply/eqP.
      rewrite -eq_adj.
      have H: Rnative i' (andB (shrBn bs (i * tableSize)) (decB (shlBn # (1) tableSize))).
        apply land_Rnative.
        apply lsr_repr=> //.
        rewrite /natural_repr.
        apply/existsP.
        exists # (i * tableSize).
        rewrite /native_repr.
        rewrite toInt_def.
        rewrite eq_refl andbT.
        by apply/eqInt32P.
        apply dec_repr.
        apply lsl_repr.
        rewrite //.
        apply one_repr.
        (* TODO: add a lemma 'natural_repr (toInt x) x'? *)
        rewrite /natural_repr.
        apply/existsP.
        exists #tableSize.
        rewrite eq_refl andbT.
        rewrite /native_repr toInt_def.
        by apply/eqInt32P.
      by apply H.
    rewrite //.
  rewrite toInt_def.
  apply/eqInt32P=> //.
  rewrite /pop_table /pop_tableAux [_ (2^tableSize) _]/=.
  admit. (* Trivial, but painful *)
  by apply toNat_andB.
Admitted.
*)

Fixpoint popAux (bs: Int32)(i: nat): Int32 :=
  match i with
  | 0 => zero
  | i'.+1 => add (pop_elem bs i') (popAux bs i')
  end.

Definition popAux_repr:
  forall n bs i,
    (i * tableSize <= wordsize)%nat ->
    Rnative n bs ->
    Rnative (popAux n i) (cardinal.popAux tableSize bs i).
Admitted.
(*
Proof.
  move=> n bs i Hi ?.
  elim: i Hi=> [Hi //=|i IH Hi].
  rewrite -fromNat0.
  apply axioms32.zero_repr.
  have Hi': (i * tableSize <= wordsize)%nat.
    apply (leq_trans (n := i.+1 * tableSize))=> //.
    rewrite leq_pmul2r=> //.
  apply add_repr=> //.
  apply (pop_elem_repr _ bs)=> //.
  by apply IH.
Qed.
*)


Definition cardinal (bs: Int32): Int32
  := popAux bs (wordsize %/ tableSize).

Lemma cardinal_repr:
  forall (bs: Int32) E, Rmachine bs E ->
    natural_repr (cardinal bs) #|E|.
Admitted.
(*
Proof.
  move=> bs E [bv [int_repr fin_repr]].
  rewrite /natural_repr.
  apply/existsP.
  exists # (#|E|).
  apply/andP; split=> //.
  rewrite -cardinal.cardinal_Rfin.
  rewrite - (@cardinal.cardinal_Rfin _ tableSize bv) => //.
  (* Refold [cardinal], for the proof's sake (and my sanity) *)
  rewrite -[cardinal _]/(popAux bs (wordsize %/ tableSize)).
  rewrite /cardinal.cardinal -[div.divn _ _]/(wordsize %/ tableSize).
  by apply (popAux_repr _ bv).
Qed.
*)

(* TODO: what do we use this one for? *)

Definition ntz (bs: Int32): Int32
  := add (toInt wordsize) (neg (cardinal (lor bs (neg bs)))).

Lemma ntz_repr:
  forall (bs: Int32) x E, Rmachine bs E -> x \in E ->
    natural_repr (ntz bs) [arg min_(k < x in E) k].
Admitted.
(*
Proof.
  move=> bs x E [bv [Hbv1 Hbv2]] Hx.
  rewrite /natural_repr.
  apply/existsP.
  exists #[arg min_(k < x in E) k].
  rewrite -(@min.ntz_repr _ bv tableSize)=> //.
  rewrite /ntz /min.ntz.
  set E' := [ set x : 'I_wordsize | getBit (min.fill_ntz bv) x ].
  have H: repr (orB bv (negB bv)) E'.
    rewrite /repr -setP /eq_mem=> i.
    by rewrite !in_set min.fill_ntz_repr.
  apply/andP.
  split=> //.
  rewrite subB_equiv_addB_negB.
  apply add_repr.
  rewrite toInt_def.
  apply/eqInt32P=> //.
  apply neg_repr.
  move: (cardinal.cardinal_repr _ tableSize (orB bv (negB bv)) E')=> H'.
  rewrite H'.
  have Hok: Rmachine (lor bs (neg bs)) E'.
    exists (orB bv (negB bv)).
    split.
    apply lor_repr.
    apply Hbv1.
    apply neg_repr.
    apply Hbv1.
    by apply H.
  move: (cardinal_repr (lor bs (neg bs)) E' Hok)=> /existsP[y /andP[Hy1 /eqP Hy2]].
  rewrite -Hy2 in Hy1.
  apply Hy1.
  trivial.
  trivial.
  trivial.
Qed.
*)

(** printing \emptyset $\emptyset$ #Ø# *)
(** printing \cap $\cap$ #∩# *)
(** printing \cup $\cup$ #∪# *)

(** Module type describing set operations & implementations using bitsets and finsets *)
Module Type SET.
  Parameter T : Type.
  Parameter eq : T -> T -> bool.
  Infix "=" := eq : SET_scope.
  Open Scope SET_scope.
  Bind Scope SET_scope with T.
  Parameter empty : T.
  Notation "\emptyset" := empty : SET_scope.
  Parameter singleton : 'I_wordsize -> T.
  Notation "{ x }" := (singleton x) : SET_scope.
  Parameter compl : T -> T.
  Notation "~ E" := (compl E) : SET_scope.
  Parameter create : bool -> T.
  Parameter get : T -> 'I_wordsize -> bool.
  Notation "x \in E" := (get E x) : SET_scope.
  Parameter inter : T -> T -> T.
  Notation "E1 \cap E2" := (inter E1 E2) (at level 0) : SET_scope.
  Parameter keep_min : forall (E: T) x, x \in E -> T.
  Notation "{ min E }" := (keep_min E) : SET_scope.
  Parameter insert : T -> 'I_wordsize -> T.
  Parameter remove : T -> 'I_wordsize -> T.
  Parameter symdiff : T -> T -> T.
  Notation "E1 \delta E2" := (symdiff E1 E2) (at level 0) : SET_scope.
  Parameter union : T -> T -> T.
  Notation "E1 \cup E2" := (union E1 E2) (at level 0) : SET_scope.
  Parameter cardinal : T -> nat.
  Notation "| E |" := (cardinal E) (at level 30) : SET_scope.
End SET.

Module Finset <: SET.
  Definition T := {set 'I_wordsize}.
  Definition eq (E: T) (E': T) := E == E'.
  Definition empty : T := set0.
  Definition singleton (x: 'I_wordsize) : T := [set x].
  Definition compl (E: T) := ~: E.
  Definition create b := if b then [ set : 'I_wordsize ] else set0.
  Definition get (E: T) x := x \in E.
  Definition inter (E1: T) E2 := E1 :&: E2.
  Definition keep_min (E: T) (x: 'I_wordsize) (Hx: get E x): T := [set [arg min_(k < x in E) k]].
  Definition insert (E: T) k := k |: E.
  Definition remove (E: T) k := E :\ k.
  Definition symdiff (E1: T) E2 := ((E2 :\: E1) :|: (E1 :\: E2)).
  Definition union (E1: T) E2 := E1 :|: E2.
  Definition cardinal (E: T) := #|E|.
End Finset.

Module Bitset <: SET.
  Definition T := Int32.
  Definition eq (E: T) (E': T) := eq E E'.
  Definition empty := zero.
  Definition singleton := singleton.
  Definition compl := compl.
  Definition create := create.
  Definition get := get.
  Definition inter := inter.
  Definition keep_min (E: T) (x: 'I_wordsize) (Hx: get E x): T := keep_min E.
  Definition insert E (x: 'I_wordsize) := insert E (toInt x).
  Definition remove E (x: 'I_wordsize) := remove E (toInt x).
  Definition symdiff := symdiff.
  Definition union := union.
  Definition cardinal (E: T) := fromInt (cardinal E).
End Bitset.
*)
