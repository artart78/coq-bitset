From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import bitset props.bineqs props.getbit spec.

(** * An axiomatization of OCaml native integers *)

(* TODO: this module should be moved (as a single file, not a module)
   to coq:bits, as a potential representation. *)

Module BitsRepr.

(** ** Base type and operations *)

Definition wordsize := 63.

Axiom Int63: Type.
Extract Inlined Constant Int63 => "int".

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

Axiom lsr: Int63 -> Int63 -> Int63.
Extract Inlined Constant lsr => "(lsr)".

Axiom lsl: Int63 -> Int63 -> Int63.
Extract Inlined Constant lsl => "(lsl)".

Axiom lneg: Int63 -> Int63.
Extract Inlined Constant lneg => "-".

(* TODO: do we really need this axiom? *)
Axiom ldec: Int63 -> Int63.
Extract Inlined Constant ldec => "(fun x -> x - 1)".

Axiom ladd: Int63 -> Int63 -> Int63.
Extract Inlined Constant ladd => "(+)".

(** We can convert to and from the axiomatized [Int63] and our
    bitvectors: in fact, they are isomorphic. *)

Axiom zero : Int63.
Extract Inlined Constant zero => "0".

Axiom one : Int63.
Extract Inlined Constant one => "1".

Axiom succ : Int63 -> Int63.
Extract Inlined Constant succ => "(fun x -> x + 1)".

Fixpoint toInt (bs: seq bool)(k: Int63): Int63 :=
  match bs with
    | [::] => zero
    | [:: false & bs] => toInt bs (succ k)
    | [:: true & bs ] => lor (lsl one k) (toInt bs (succ k))
  end.

(** Careful, this is painfully slow... Any workaround? *)
Definition toInt63 (bs: BITS wordsize): Int63
  := toInt bs zero. 


Fixpoint fromInt (n: Int63)(k: nat): seq bool :=
  match k with 
    | 0 => [::]
    | k.+1 =>
      [:: leq (land (lsr n (toInt63 #(63 - k.+1))) one) one &
          fromInt n k]
  end.

Lemma fromInt63P {k} (n: Int63): size (fromInt n k) == k.
Proof.
  elim: k=> // [k IH].
Qed.

Canonical fromInt63 (n: Int63): BITS 63
  := Tuple (fromInt63P n).


(** ** Axiomatized equivalence with BITS *)

(** We say that an [n : Int63] is the representation of a bitvectir
[bs : BITS 63] if they satisfy the axiom [repr_native]. Morally, it
means that both represent the same number (ie. same 63 booleans). *)

Axiom native_repr: Int63 -> BITS wordsize -> Prop.

Definition natural_repr: Int63 -> nat -> Prop :=
  fun i n =>
    exists bs, native_repr i bs /\ # n = bs.

(** We postulate that OCaml's operations are a refinement of the
    coq-bits ones. *)

Axiom lnot_repr: forall i bs, native_repr i bs -> native_repr (lnot i) (invB bs).
Axiom land_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> native_repr (land i i') (andB bs bs').
Axiom lor_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> native_repr (lor i i') (orB bs bs').
Axiom lxor_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> native_repr (lxor i i') (xorB bs bs').
Axiom lsr_repr: forall i j bs k,
                  native_repr i bs -> natural_repr j k ->
                  native_repr (lsr i j) (shrBn bs k).
Axiom lsl_repr: forall i j bs k,
                  native_repr i bs -> natural_repr j k ->
                  native_repr (lsl i j) (shlBn bs k).
Axiom lneg_repr: forall i bs, native_repr i bs -> native_repr (lneg i) (negB bs).
Axiom ldec_repr: forall i bs, native_repr i bs -> native_repr (ldec i) (decB bs).
Axiom leq_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> (leq i i') = (bs == bs').
Axiom ladd_repr: forall i i' bs bs', native_repr i bs -> native_repr i' bs' -> native_repr (ladd i i') (addB bs bs').

(** Our conversion, being the identity, respect this relation. *)

Axiom zero_repr: native_repr zero #0.
Axiom one_repr: native_repr one #1.

(* TODO: this one won't be easy *)
Lemma toInt63_repr: forall bs, native_repr (toInt63 bs) bs.
  admit.
Admitted.

(* TODO: this one won't be easy *)
Lemma fromInt63_repr: forall i bs, native_repr i bs -> fromInt63 i = bs.
Admitted.

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


(** We go from Coq's [nat] to [Int63] by (brutally) collapsing [nat]
    to [int]: *)

Extract Inductive nat => int [ "0" "succ" ]
                             "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Axiom toInt63: nat -> BitsRepr.Int63.
(*  := BitsRepr.toInt63 #n. *)

Extract Inlined Constant toInt63 => "".

Axiom toInt63_def : forall n, toInt63 n = BitsRepr.toInt63 (# n).


Axiom fromInt63: BitsRepr.Int63 -> nat.
(*  := toNat (BitsRepr.fromInt63 n). *)

Extract Inlined Constant fromInt63 => "".

Axiom fromInt63_def : forall n, fromInt63 n = toNat (BitsRepr.fromInt63 n).

(** ** Equality *)

Lemma eq_repr: forall i i' E E', native_repr i E -> native_repr i' E' -> (BitsRepr.leq i i') = (E == E').
Proof.
  move=> i i' E E' [bv [Hbv1 Hbv2]] [bv' [Hbv'1 Hbv'2]].
  rewrite (BitsRepr.leq_repr _ _ bv bv')=> //.
  by rewrite (spec.eq_repr _ _ _ E E').
Qed.

(** ** Zero *)

Lemma zero_repr:
  native_repr BitsRepr.zero set0.
Proof.
  exists (zero BitsRepr.wordsize).
  split.
  rewrite -fromNat0.
  apply BitsRepr.zero_repr.
  exact: empty_repr.
Qed.

(** ** Singleton *)

Lemma singleton_repr:
  forall (x: 'I_BitsRepr.wordsize),
    native_repr (BitsRepr.lsl BitsRepr.one (toInt63 x)) [set x].
Proof.
  move=> x.
  exists (shlBn #1 x).
  split.
  * apply BitsRepr.lsl_repr.
    apply BitsRepr.one_repr.
    by eexists; split; first by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
  * rewrite getBit_shlBn=> //.
    apply singleton_repr.
Qed.

(** ** Left & right shift *)

Lemma sl_repr:
  forall i E, native_repr i E ->
    native_repr (BitsRepr.lsl i BitsRepr.one) [set i : 'I_BitsRepr.wordsize | 0 < i & @inord BitsRepr.wordsize.-1 i.-1 \in E].
Proof.
  move=> i E [bv [r_native r_set]].
  exists (shlBn bv 1); split.
  * apply: BitsRepr.lsl_repr;
      first by assumption.
    eexists; split;
      first by apply BitsRepr.one_repr.
    done.
  * have H: BitsRepr.wordsize = BitsRepr.wordsize.-1.+1 by compute.
    have ->: [set i0 : 'I_BitsRepr.wordsize | 0 < i0 & inord i0.-1 \in E]
           = [set i0 : 'I_BitsRepr.wordsize | 0 < i0 & cast_ord H (inord i0.-1) \in E].
      rewrite -setP /eq_mem=> x.
      rewrite !in_set.
      have ->: cast_ord H (inord x.-1) = inord x.-1.
        apply ord_inj.
        by rewrite nat_cast_ord.
      by rewrite //.
    by apply shift.sl_repr.
Qed.

Lemma sr_repr:
  forall i E, native_repr i E ->
    native_repr (BitsRepr.lsr i BitsRepr.one) [set i : 'I_BitsRepr.wordsize | i < BitsRepr.wordsize.-1 & @inord BitsRepr.wordsize.-1 i.+1 \in E].
Proof.
  move=> i E [bv [r_native r_set]].
  exists (shrBn bv 1); split.
  * apply: BitsRepr.lsr_repr; 
      first by assumption.
    eexists; split; 
      first by apply BitsRepr.one_repr.
    done.
  * have H: BitsRepr.wordsize = BitsRepr.wordsize.-1.+1 by compute.
    have ->: [set i0 : 'I_BitsRepr.wordsize | i0 < BitsRepr.wordsize.-1 & inord i0.+1 \in E]
           = [set i0 : 'I_BitsRepr.wordsize | i0 < BitsRepr.wordsize.-1 & cast_ord H (inord i0.+1) \in E].
      rewrite -setP /eq_mem=> x.
      rewrite !in_set.
      have ->: cast_ord H (inord x.+1) = inord x.+1.
        apply ord_inj.
        by rewrite nat_cast_ord.
      by rewrite //.
    by apply shift.sr_repr.
Qed.

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
      apply BitsRepr.ldec_repr.
      by rewrite toInt63_def;
         apply BitsRepr.toInt63_repr.
    + (* Case: b ~ false *)
      by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
Qed.

(** ** Querying *)

Definition get (bs: BitsRepr.Int63) (k: 'I_BitsRepr.wordsize): bool
  := BitsRepr.leq (BitsRepr.land (BitsRepr.lsr bs (toInt63 k)) BitsRepr.one) BitsRepr.one.

Lemma get_repr:
  forall i E (k: 'I_BitsRepr.wordsize), native_repr i E ->
    get i k = (k \in E).
Proof.
  move=> i E k H.
  rewrite /get.
  move: H=> [bv [Hbv1 Hbv2]].
  rewrite (BitsRepr.leq_repr _ _ (andB (shrBn bv k) #1) #1);
    last by apply BitsRepr.one_repr.
  apply get.get_repr=> //.
  apply BitsRepr.land_repr;
     last by apply BitsRepr.one_repr.
  apply BitsRepr.lsr_repr=> //.
  eexists; split => //;
    first by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
Qed.

(** ** Intersection *)

Definition inter (bs: BitsRepr.Int63) (bs': BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.land bs bs'.

Lemma inter_repr:
  forall i i' E E', native_repr i E -> native_repr i' E' ->
    native_repr (inter i i') (E :&: E').
Proof.
  move=> i i' E E' H H'.
  rewrite /native_repr.
  move: H=> [bv [Hbv1 Hbv2]].
  move: H'=> [bv' [Hbv'1 Hbv'2]].
  exists (inter.inter bv bv').
  split.
  apply BitsRepr.land_repr=> //.
  by apply (inter.inter_repr _ bv bv').
Qed.

(** ** Minimal element *)

Definition keep_min (bs: BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.land bs (BitsRepr.lneg bs).

Lemma keep_min_repr:
  forall i E x, native_repr i E -> x \in E ->
    native_repr (keep_min i) [set [arg min_(k < x in E) k]].
Proof.
  move=> i E x H Hx.
  move: H=> [bv [Hbv1 Hbv2]].
  exists (keep_min.keep_min bv).
  split.
  apply BitsRepr.land_repr=> //.
  apply BitsRepr.lneg_repr=> //.
  by apply keep_min.keep_min_repr.
Qed.

(** ** Insertion *)

Definition set (bs: BitsRepr.Int63) k (b: bool): BitsRepr.Int63
  := if b then 
       BitsRepr.lor bs (BitsRepr.lsl (toInt63 1) k) 
     else
       BitsRepr.land bs (BitsRepr.lnot (BitsRepr.lsl (toInt63 1) k)).

Lemma set_repr:
  forall i (k: 'I_BitsRepr.wordsize) (b: bool) E, native_repr i E ->
    native_repr (set i (toInt63 k) b) (if b then (k |: E) else (E :\ k)).
Proof.
  move=> i k b E [bv [Hbv1 Hbv2]].
  exists (set.set bv k b).
  split.
  rewrite /set /set.set.
  case: b.
    apply BitsRepr.lor_repr=> //.
    apply BitsRepr.lsl_repr=> //.
    + by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
    + by eexists; split; first by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
    apply BitsRepr.land_repr=> //.
    apply BitsRepr.lnot_repr=> //.
    apply BitsRepr.lsl_repr=> //.
    rewrite toInt63_def; apply BitsRepr.toInt63_repr=> //.
    by eexists; split; first by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
  by apply set.set_repr.
Qed.

(** ** Symmetrical difference *)

Definition symdiff (bs: BitsRepr.Int63) (bs': BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.lxor bs bs'.

Lemma symdiff_repr:
  forall i i' E E', native_repr i E -> native_repr i' E' ->
    native_repr (symdiff i i') ((E :\: E') :|: (E' :\: E)).
Proof.
  move=> i i' E E' [bv [Hbv1 Hbv2]] [bv' [Hbv'1 Hbv'2]].
  exists (symdiff.symdiff bv bv').
  split.
  apply BitsRepr.lxor_repr=> //.
  by apply symdiff.symdiff_repr.
Qed.

(** ** Union *)

Definition union (bs: BitsRepr.Int63) (bs': BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.lor bs bs'.

Lemma union_repr:
  forall i i' E E', native_repr i E -> native_repr i' E' ->
    native_repr (union i i') (E :|: E').
Proof.
  move=> i i' E E' [bv [Hbv1 Hbv2]] [bv' [Hbv'1 Hbv'2]].
  exists (union.union bv bv').
  split.
  apply BitsRepr.lor_repr=> //.
  by apply union.union_repr.
Qed.

(** ** Subset *)

Lemma subset_repr: forall (bs bs': BitsRepr.Int63) E E',
  native_repr bs E -> native_repr bs' E' ->
    (BitsRepr.leq (BitsRepr.land bs bs') bs) =
      (E \subset E').
Proof.
  move=> bs bs' E E' HE HE'.
  rewrite (eq_repr _ _ (E :&: E') E)=> //.
  apply/eqP.
  case: setIidPl=> //=.
  apply inter_repr=> //.
Qed.

(** ** Cardinality *)

Definition pop_table := Eval compute in (mkseq (fun i => toInt63 (count_mem true (fromNat (n := 3) i)
)) (2^3)).

Definition pop_elem (bs: BitsRepr.Int63)(i: nat): BitsRepr.Int63
  := let x := BitsRepr.land (BitsRepr.lsr bs (toInt63 (i * 3))) 
                            (BitsRepr.ldec (BitsRepr.lsl BitsRepr.one (toInt63 3))) in
     nth BitsRepr.zero pop_table (fromInt63 x).

Lemma pop_elem_repr: 
  forall n bs i,
    BitsRepr.native_repr n bs ->
    BitsRepr.native_repr (pop_elem n i) (cardinal.pop_elem 3 bs i).
Proof.
  move=> n bs i ?.
  rewrite /pop_elem/cardinal.pop_elem.
  have ->:
       ((fromInt63
          (BitsRepr.land (BitsRepr.lsr n (toInt63 (i * 3)))
                         (BitsRepr.ldec (BitsRepr.lsl BitsRepr.one (toInt63 3))))) =
       (toNat (andB (shrBn bs (i * 3)) (decB (shlBn # (1) 3))))).
  rewrite fromInt63_def; apply f_equal.
  apply BitsRepr.fromInt63_repr.
  apply BitsRepr.land_repr.
  * by apply BitsRepr.lsr_repr=> //;
    eexists; split; first by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
  * apply BitsRepr.ldec_repr;
    apply BitsRepr.lsl_repr;
       first by apply BitsRepr.one_repr.
    by eexists; split; first by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
  admit. (* pop_table represents cardinal.pop_table 3 ... *)
Admitted.

Fixpoint popAux (bs: BitsRepr.Int63)(i: nat): BitsRepr.Int63 :=
  match i with
  | 0 => BitsRepr.zero
  | i'.+1 => BitsRepr.ladd (pop_elem bs i') (popAux bs i')
  end.

Definition popAux_repr:
  forall n bs i,
    BitsRepr.native_repr n bs ->
    BitsRepr.native_repr (popAux n i) (cardinal.popAux 3 bs i).
Proof.
  move=> n bs i ?.
  elim: i => //=.
  rewrite -fromNat0.
  apply BitsRepr.zero_repr.
  move=> i IH.
  apply BitsRepr.ladd_repr=> //.
  by apply (pop_elem_repr _ bs).
Qed.

Definition cardinal (bs: BitsRepr.Int63): BitsRepr.Int63
  := Eval compute in popAux bs 21.

Lemma cardinal_repr:
  forall (bs: BitsRepr.Int63) E, native_repr bs E ->
    BitsRepr.natural_repr (cardinal bs) #|E|.
Proof.
  move=> bs E [bv [int_repr fin_repr]].
  rewrite /BitsRepr.natural_repr.
  exists # (#|E|).
  split=> //.
  rewrite - (@cardinal.cardinal_repr _ 3 bv) => //.
  (* Refold [cardinal], for the proof's sake (and my sanity) *)
  rewrite -[cardinal _]/(popAux bs 21).
  rewrite /cardinal.cardinal -[div.divn _ _]/21.
  by apply (popAux_repr _ bv).
Qed.

(* TODO: what do we use this one for? *)

Definition ntz (bs: BitsRepr.Int63): BitsRepr.Int63
  := BitsRepr.ladd (toInt63 BitsRepr.wordsize) (BitsRepr.lneg (cardinal (BitsRepr.lor bs (BitsRepr.lneg bs)))).

Lemma ntz_repr:
  forall (bs: BitsRepr.Int63) x E, native_repr bs E -> x \in E ->
    BitsRepr.natural_repr (ntz bs) [arg min_(k < x in E) k].
Proof.
  move=> bs x E [bv [Hbv1 Hbv2]] Hx.
  rewrite /BitsRepr.natural_repr.
  exists #[arg min_(k < x in E) k].
  rewrite -(min.ntz_repr _ bv 3)=> //.
  rewrite /ntz /min.ntz.
  set E' := [ set x : 'I_BitsRepr.wordsize | getBit (min.fill_ntz bv) x ].
  have H: repr (orB bv (negB bv)) E'.
    rewrite /repr -setP /eq_mem=> i.
    by rewrite !in_set min.fill_ntz_repr.
  split=> //.
  rewrite subB_equiv_addB_negB.
  apply BitsRepr.ladd_repr.
  rewrite toInt63_def.
  apply BitsRepr.toInt63_repr.
  apply BitsRepr.lneg_repr.
  move: (cardinal.cardinal_repr _ 3 (orB bv (negB bv)) E')=> H'.
  rewrite H'.
  have Hok: native_repr (BitsRepr.lor bs (BitsRepr.lneg bs)) E'.
    exists (orB bv (negB bv)).
    split.
    apply BitsRepr.lor_repr.
    apply Hbv1.
    apply BitsRepr.lneg_repr.
    apply Hbv1.
    by apply H.
  move: (cardinal_repr (BitsRepr.lor bs (BitsRepr.lneg bs)) E' Hok)=> [y [Hy1 Hy2]].
  rewrite -Hy2 in Hy1.
  apply Hy1.
  trivial.
  trivial.
  trivial.
Qed.
