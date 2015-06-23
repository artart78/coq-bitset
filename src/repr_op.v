From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import bitset spec.

(** * An axiomatization of OCaml native integers *)

(* TODO: this module should be moved (as a single file, not a module)
   to coq:bits, as a potential representation. *)

Module BitsRepr.

(** ** Base type and operations *)

Definition wordsize := 63.

Axiom Int63: Type.
Extract Inlined Constant Int63 => "int".


(** We can convert to and from the axiomatized [Int63] and our
    bitvectors: theyr are in fact the same thing. *)

Axiom toInt63: BITS wordsize -> Int63.
Extract Inlined Constant toInt63 => "".

Axiom fromInt63: Int63 -> BITS wordsize.
Extract Inlined Constant fromInt63 => "".

(** We import the following operations from OCaml: *)

Axiom leq: Int63 -> Int63 -> bool.
Extract Inlined Constant leq => "(=)".

Axiom lnot: Int63 -> Int63.
Extract Inlined Constant lnot => "lnot".

Axiom land: Int63 -> Int63 -> Int63.
Extract Inlined Constant land => "(land)".

Axiom lor: Int63 -> Int63 -> Int63.
Extract Inlined Constant lor => "(lor)".

Axiom lxor: Int63 -> Int63 -> Int63.
Extract Inlined Constant lxor => "(lxor)".

Axiom lsr: Int63 -> nat -> Int63.
Extract Inlined Constant lsr => "(lsr)".

Axiom lsl: Int63 -> nat -> Int63.
Extract Inlined Constant lsl => "(lsl)".

Axiom lneg: Int63 -> Int63.
Extract Inlined Constant lneg => "-".

(* TODO: do we really need this axiom? *)
Axiom ldec: Int63 -> Int63.
Extract Inlined Constant ldec => "(fun x -> x - 1)".

(** ** Axiomatized equivalence with BITS *)

(** We say that an [n : Int63] is the representation of a bitvectir
[bs : BITS 63] if they satisfy the axiom [repr_native]. Morally, it
means that both represent the same number (ie. same 63 booleans). *)

Axiom native_repr: Int63 -> (BITS wordsize) -> Prop.

(** Our conversion, being the identity, respect this relation. *)

Axiom toInt63_repr: forall k, native_repr (toInt63 k) k.
Axiom fromInt63_repr: forall i bs, native_repr i bs -> fromInt63 i = bs.

(** We postulate that OCaml's operations are a refinement of the
    coq-bits ones. *)

Axiom lnot_repr: forall i bs, native_repr i bs -> native_repr (lnot i) (invB bs).
Axiom land_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> native_repr (land i i') (andB bs bs').
Axiom lor_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> native_repr (lor i i') (orB bs bs').
Axiom lxor_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> native_repr (lxor i i') (xorB bs bs').
Axiom lsr_repr: forall i bs k, native_repr i bs -> native_repr (lsr i k) (shrBn bs k).
Axiom lsl_repr: forall i bs k, native_repr i bs -> native_repr (lsl i k) (shlBn bs k).
Axiom lneg_repr: forall i bs, native_repr i bs -> native_repr (lneg i) (negB bs).
Axiom ldec_repr: forall i bs, native_repr i bs -> native_repr (ldec i) (decB bs).
Axiom leq_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> (leq i i') = (bs == bs').

End BitsRepr.

(** * A formalisation of bitsets using OCaml's integers *)

(** 
    
    We establish a relation between OCaml's types (which extracts
    efficiently to machine-native datatypes) and the finset
    library. This is achieved by composing the representation of [BITS
    63] with OCaml's [int] (defined in [coq:bits]) and the
    representation of [finset] with [BITS n].

 *)


(* TODO: is there anything isomorphic but more sexy than [{set
ordinal_finType BitsRepr.wordsize}] *)

Definition native_repr
           (n: BitsRepr.Int63)
           (E: {set ordinal_finType BitsRepr.wordsize}): Prop :=
  exists bv, BitsRepr.native_repr n bv /\ repr bv E.


(** We go from Coq's [nat] to [Int63] through [BITS 63]. *)

Definition toInt63 (n: nat): BitsRepr.Int63
  := BitsRepr.toInt63 #n.

Definition fromInt63 (n: BitsRepr.Int63): nat
  := toNat (BitsRepr.fromInt63 n).


(** ** Complement *)

Definition compl (bs: BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.lnot bs.

Lemma compl_repr:
  forall i E, native_repr i E -> native_repr (compl i) (~: E).
Proof.
  move=> i E [bv [r_native r_set]].
  exists (invB bv); split.
  * rewrite /compl; apply BitsRepr.lnot_repr => //.
  * apply compl.compl_repr => //.
Qed.

(** ** Set creation *)

Definition create (b: bool): BitsRepr.Int63
  := if b then BitsRepr.ldec (toInt63 0) else (toInt63 0).

Lemma create_repr:
  forall (b: bool),
    native_repr (create b) (if b then [ set : 'I_BitsRepr.wordsize ] else set0).
Proof.
  move=> b.
  exists (create.create b). split; last first.
  * apply create.create_repr => //.
  * rewrite /create/create.create; case: b.
    + (* Case: b ~ true *)
      by apply BitsRepr.ldec_repr;
         apply BitsRepr.toInt63_repr.
    + (* Case: b ~ false *)
      by apply BitsRepr.toInt63_repr.
Qed.

(** ** Querying *)

Definition get (bs: BitsRepr.Int63) (k: 'I_BitsRepr.wordsize): bool
  := BitsRepr.leq (BitsRepr.land (BitsRepr.lsr bs k) (toInt63 1)) (toInt63 1).

Lemma get_repr:
  forall i E (k: 'I_BitsRepr.wordsize), native_repr i E ->
    get i k = (k \in E).
Proof.
Admitted.
(* TODO: Update 
  move=> i E k H.
  rewrite /get.
  rewrite (leq_repr _ _ (andB (shrBn (toBs i) k) #1) #1).
  apply get.get_repr.
  apply repr_ax=> //.
  apply land_repr.
  apply lsr_repr.
  apply native_repr_ax.
  apply toInt63_repr.
  by apply toInt63_repr.
Qed. *)

(** ** Intersection *)

Definition inter (bs: BitsRepr.Int63) (bs': BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.land bs bs'.

Lemma inter_repr:
  forall i i' E E', native_repr i E -> native_repr i' E' ->
    native_repr (inter i i') (E :&: E').
Proof.
Admitted.
(* TODO: Update
  move=> i i' E E' H H'.
  apply (native_repr_ax (inter i i') (inter.inter (toBs i) (toBs i'))).
  apply land_repr.
  apply native_repr_ax.
  apply native_repr_ax.
  apply inter.inter_repr.
  apply repr_ax=> //.
  by apply repr_ax.
Qed. *)


(** ** Minimal element *)

Definition keep_min (bs: BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.land bs (BitsRepr.lneg bs).

Lemma keep_min_repr:
  forall i E x, native_repr i E -> x \in E ->
    native_repr (keep_min i) [set [arg min_(k < x in E) k]].
Proof.
Admitted.
(* TODO: Update 
  move=> i E x H Hx.
  apply (native_repr_ax (keep_min i) (keep_min.keep_min (toBs i))).
  apply land_repr.
  apply native_repr_ax.
  apply lneg_repr.
  apply native_repr_ax.
  apply keep_min.keep_min_repr=> //.
  by apply repr_ax=> //.
Qed.*)

(** ** Insertion *)

Definition set (bs: BitsRepr.Int63) k (b: bool): BitsRepr.Int63
  := if b then 
       BitsRepr.lor bs (BitsRepr.lsl (toInt63 1) k) 
     else
       BitsRepr.land bs (BitsRepr.lnot (BitsRepr.lsl (toInt63 1) k)).

Lemma set_repr:
  forall i (k: 'I_BitsRepr.wordsize) (b: bool) E, native_repr i E ->
    native_repr (set i k b) (if b then (k |: E) else (E :\ k)).
Proof.
Admitted.
(* TODO: Update
  move=> i k b E H.
  apply (native_repr_ax (set i k b) (set.set (toBs i) k b)).
  rewrite /set /set.set.
  case: b.
    apply lor_repr.
    apply native_repr_ax.
    apply lsl_repr.
    apply toInt63_repr.
    apply land_repr.
    apply native_repr_ax.
    apply lnot_repr.
    apply lsl_repr.
    apply toInt63_repr.
  apply set.set_repr.
  by apply repr_ax=> //.
Qed. *)

(** ** Symmetrical difference *)

Definition symdiff (bs: BitsRepr.Int63) (bs': BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.lxor bs bs'.

Lemma symdiff_repr:
  forall i i' E E', native_repr i E -> native_repr i' E' ->
    native_repr (symdiff i i') ((E :\: E') :|: (E' :\: E)).
Proof.
Admitted.
(* TODO: Update
  move=> i i' E E' H H'.
  apply (native_repr_ax (symdiff i i') (symdiff.symdiff (toBs i) (toBs i'))).
  apply lxor_repr.
  apply native_repr_ax.
  apply native_repr_ax.
  apply symdiff.symdiff_repr.
  apply repr_ax=> //.
  by apply repr_ax.
Qed. *)

(** ** Union *)

Definition union (bs: BitsRepr.Int63) (bs': BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.lor bs bs'.

Lemma union_repr:
  forall i i' E E', native_repr i E -> native_repr i' E' ->
    native_repr (union i i') (E :|: E').
Proof.
Admitted.
(* TODO: Update 
  move=> i i' E E' H H'.
  apply (native_repr_ax (union i i') (union.union (toBs i) (toBs i'))).
  apply lor_repr.
  apply native_repr_ax.
  apply native_repr_ax.
  apply union.union_repr.
  apply repr_ax=> //.
  by apply repr_ax.
Qed. *)

(** ** Cardinality *)

Definition pop_table := cardinal.pop_table 3.

Definition pop_elem (bs: BitsRepr.Int63)(i: nat): nat
  := let x := BitsRepr.land (BitsRepr.lsr bs (i * 3)) 
                            (BitsRepr.ldec (BitsRepr.lsl (toInt63 1) 3)) in
     nth 0 pop_table (fromInt63 x).

Lemma pop_elem_repr: 
  forall n bs i,
    BitsRepr.native_repr n bs ->
    pop_elem n i = cardinal.pop_elem 3 bs i.
Proof.
  move=> n bs i ?.
  rewrite /pop_elem/cardinal.pop_elem.
  suff ->:
       ((fromInt63
          (BitsRepr.land (BitsRepr.lsr n (i * 3))
                         (BitsRepr.ldec (BitsRepr.lsl (toInt63 1) 3)))) =
       (toNat (andB (shrBn bs (i * 3)) (decB (shlBn # (1) 3)))))
       by done.
  rewrite /fromInt63; apply f_equal.
  apply BitsRepr.fromInt63_repr.
  apply BitsRepr.land_repr.
  * by apply BitsRepr.lsr_repr=> //.
  * by apply BitsRepr.ldec_repr;
       apply BitsRepr.lsl_repr;
       apply BitsRepr.toInt63_repr.
Qed.

Fixpoint popAux (bs: BitsRepr.Int63)(i: nat): nat :=
  match i with
  | 0 => 0
  | i'.+1 => (pop_elem bs i') + (popAux bs i')
  end.

Definition popAux_repr:
  forall n bs i,
    BitsRepr.native_repr n bs ->
    popAux n i = cardinal.popAux 3 bs i.
Proof.
  move=> n bs i ?.
  elim: i => //= [i IH].
  rewrite (pop_elem_repr _ bs) //. 
  rewrite IH //.
Qed.
  

Definition cardinal  (bs: BitsRepr.Int63): nat
  := Eval compute in popAux bs 21.

Lemma cardinal_repr:
  forall (bs: BitsRepr.Int63) E, native_repr bs E ->
    cardinal bs = #|E|.
Proof.
  move=> bs E [bv [int_repr fin_repr]].
  rewrite - (@cardinal.cardinal_repr _ 3 bv) => //.
  (* Refold [cardinal], for the proof's sake (and my sanity) *)
  rewrite -[cardinal _]/(popAux bs 21).
  rewrite /cardinal.cardinal -[div.divn _ _]/21.
  rewrite (popAux_repr _ bv) //.
Qed.


(* TODO: what do we use this one for? *)

Definition ntz (bs: BitsRepr.Int63): nat
  := 63 - (cardinal (BitsRepr.lor bs (BitsRepr.lneg bs))).

Lemma ntz_repr:
  forall (bs: BitsRepr.Int63) x E, native_repr bs E -> x \in E ->
    ntz bs = [arg min_(k < x in E) k].
Proof.
Admitted.
(* TODO: Update
  move=> bs x E HE Hx.
  rewrite -(min.ntz_repr _ (toBs bs) 3)=> //.
  rewrite /ntz /min.ntz.
  set E' := [ set x : 'I_BitsRepr.wordsize | getBit (min.fill_ntz (toBs bs)) x ].
  have H: repr (orB (toBs bs) (negB (toBs bs))) E'.
    rewrite /repr -setP /eq_mem=> i.
    rewrite !in_set min.fill_ntz_repr //.
  rewrite (cardinal_repr _ E').
  rewrite (cardinal.cardinal_repr _ _ _ E')=> //.
  apply (native_repr_ax _ (orB (toBs bs) (negB (toBs bs))))=> //.
  apply lor_repr.
  apply native_repr_ax.
  apply lneg_repr.
  apply native_repr_ax.
  by apply repr_ax=> //.
Qed. *)