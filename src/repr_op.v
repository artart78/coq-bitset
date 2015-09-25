Require Import FMapList OrderedType OrderedTypeEx Compare_dec Peano_dec.
From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset div.
From Bits
     Require Import bits extraction.axioms32.
Require Import props.bineqs props.getbit spec.

Require create get set inter union symdiff compl keep_min min cardinal shift.

(** * A formalisation of bitsets using OCaml's integers *)

(** 
    
    We establish a relation between OCaml's types (which extracts
    efficiently to machine-native datatypes) and the finset
    library. This is achieved by composing the representation of [BITS
    32] with OCaml's [int] (defined in [coq:bits]) and the
    representation of [finset] with [BITS n].

 *)

Definition machine_repr
           (n: Int)
           (E: {set 'I_wordsize}): Prop :=
  exists bv, native_repr n bv /\ repr bv E.


(** We go from Coq's [nat] to [Int] by (brutally) collapsing [nat]
    to [int]: *)

Extract Inductive nat => int [ "0" "succ" ]
                             "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Axiom toInt: nat -> Int.

Extract Inlined Constant toInt => "".

Axiom toInt_def : forall n, toInt n = bitsToInt (# n).


Axiom fromInt: Int -> nat.

Extract Inlined Constant fromInt => "".

Axiom fromInt_def : forall n, fromInt n = toNat (bitsFromInt n).

(** ** Equality *)

Lemma eq_repr: forall i i' E E', machine_repr i E -> machine_repr i' E' -> (eq i i') = (E == E').
Proof.
  move=> i i' E E' [bv [Hbv1 Hbv2]] [bv' [Hbv'1 Hbv'2]].
  rewrite (axioms32.eq_repr _ _ bv bv')=> //.
  by rewrite -(spec.eq_repr _ bv bv' E E').
Qed.

(** ** Zero *)

Lemma zero_repr:
  machine_repr zero set0.
Proof.
  exists (spec.zero wordsize).
  split.
  rewrite -fromNat0.
  apply zero_repr.
  exact: empty_repr.
Qed.

(** ** Singleton *)

Lemma singleton_repr:
  forall (x: 'I_wordsize),
    machine_repr (lsl one (toInt x)) [set x].
Proof.
  move=> x.
  exists (shlBn #1 x).
  split.
  * apply lsl_repr=> //.
    apply one_repr.
    apply/existsP; exists # (x); apply/andP; split=> //.
    apply/eqIntP.
    rewrite toInt_def=> //.
  * rewrite getBit_shlBn=> //.
    apply singleton_repr.
Qed.

(** ** Left & right shift *)

Lemma sl_repr:
  forall i E, machine_repr i E ->
    machine_repr (lsl i one) [set i : 'I_wordsize | 0 < i & @inord wordsize.-1 i.-1 \in E].
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

Lemma sr_repr:
  forall i E, machine_repr i E ->
    machine_repr (lsr i one) [set i : 'I_wordsize | i < wordsize.-1 & @inord wordsize.-1 i.+1 \in E].
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

(** ** Complement *)

Definition compl (bs: Int): Int
  := lnot bs.

Lemma compl_repr:
  forall i E, machine_repr i E -> machine_repr (compl i) (~: E).
Proof.
  move=> i E [bv [r_native r_set]].
  exists (invB bv); split.
  * rewrite /compl; apply lnot_repr => //.
  * apply compl.compl_repr => //.
Qed.

(** ** Set creation *)

Definition create (b: bool): Int
  := if b then dec (toInt 0) else (toInt 0).

Lemma create_repr:
  forall (b: bool),
    machine_repr (create b) (if b then [ set : 'I_wordsize ] else set0).
Proof.
  move=> b.
  exists (create.create b). split; last first.
  * apply create.create_repr => //.
  * rewrite /create/create.create; case: b.
    + (* Case: b ~ true *)
      apply dec_repr.
      by rewrite toInt_def;
         apply/eqIntP.
    + (* Case: b ~ false *)
      by rewrite toInt_def; apply/eqIntP.
Qed.

(** ** Querying *)

Definition get (bs: Int) (k: 'I_wordsize): bool
  := eq (land (lsr bs (toInt k)) one) one.

Lemma get_repr:
  forall i E (k: 'I_wordsize), machine_repr i E ->
    get i k = (k \in E).
Proof.
  move=> i E k H.
  rewrite /get.
  move: H=> [bv [Hbv1 Hbv2]].
  rewrite (axioms32.eq_repr _ _ (andB (shrBn bv k) #1) #1);
    last by apply one_repr.
  apply get.get_repr=> //.
  apply land_repr;
     last by apply one_repr.
  apply lsr_repr=> //.
  apply/existsP; exists # (k); apply/andP; split=> //.
  rewrite toInt_def.
  by apply/eqIntP.
Qed.

(** ** Intersection *)

Definition inter (bs: Int) (bs': Int): Int
  := land bs bs'.

Lemma inter_repr:
  forall i i' E E', machine_repr i E -> machine_repr i' E' ->
    machine_repr (inter i i') (E :&: E').
Proof.
  move=> i i' E E' H H'.
  rewrite /machine_repr.
  move: H=> [bv [Hbv1 Hbv2]].
  move: H'=> [bv' [Hbv'1 Hbv'2]].
  exists (inter.inter bv bv').
  split.
  apply land_repr=> //.
  by apply (inter.inter_repr _ bv bv').
Qed.

(** ** Minimal element *)

Definition keep_min (bs: Int): Int
  := land bs (neg bs).

Lemma keep_min_repr:
  forall i E x, machine_repr i E -> x \in E ->
    machine_repr (keep_min i) [set [arg min_(k < x in E) k]].
Proof.
  move=> i E x H Hx.
  move: H=> [bv [Hbv1 Hbv2]].
  exists (keep_min.keep_min bv).
  split.
  apply land_repr=> //.
  apply neg_repr=> //.
  by apply keep_min.keep_min_repr.
Qed.

(** ** Insertion *)

Definition set (bs: Int) k (b: bool): Int
  := if b then 
       lor bs (lsl (toInt 1) k) 
     else
       land bs (lnot (lsl (toInt 1) k)).

Lemma set_repr:
  forall i (k: 'I_wordsize) (b: bool) E, machine_repr i E ->
    machine_repr (set i (toInt k) b) (if b then (k |: E) else (E :\ k)).
Proof.
  move=> i k b E [bv [Hbv1 Hbv2]].
  exists (set.set bv k b).
  split.
  rewrite /set /set.set.
  case: b.
    apply lor_repr=> //.
    apply lsl_repr=> //.
    + by rewrite toInt_def; apply/eqIntP.
    + rewrite toInt_def; apply/existsP; exists # (k); apply/andP; split=> //.
      by apply/eqIntP.
    apply land_repr=> //.
    apply lnot_repr=> //.
    apply lsl_repr=> //.
    by rewrite toInt_def; apply/eqIntP.
    rewrite toInt_def; apply/existsP; exists # (k); apply/andP; split=> //.
      by apply/eqIntP.
  by apply set.set_repr.
Qed.

(** ** Symmetrical difference *)

Definition symdiff (bs: Int) (bs': Int): Int
  := lxor bs bs'.

Lemma symdiff_repr:
  forall i i' E E', machine_repr i E -> machine_repr i' E' ->
    machine_repr (symdiff i i') ((E :\: E') :|: (E' :\: E)).
Proof.
  move=> i i' E E' [bv [Hbv1 Hbv2]] [bv' [Hbv'1 Hbv'2]].
  exists (symdiff.symdiff bv bv').
  split.
  apply lxor_repr=> //.
  by apply symdiff.symdiff_repr.
Qed.

(** ** Union *)

Definition union (bs: Int) (bs': Int): Int
  := lor bs bs'.

Lemma union_repr:
  forall i i' E E', machine_repr i E -> machine_repr i' E' ->
    machine_repr (union i i') (E :|: E').
Proof.
  move=> i i' E E' [bv [Hbv1 Hbv2]] [bv' [Hbv'1 Hbv'2]].
  exists (union.union bv bv').
  split.
  apply lor_repr=> //.
  by apply union.union_repr.
Qed.

(** ** Subset *)

Lemma subset_repr: forall (bs bs': Int) E E',
  machine_repr bs E -> machine_repr bs' E' ->
    (eq (land bs bs') bs) =
      (E \subset E').
Proof.
  move=> bs bs' E E' HE HE'.
  rewrite (eq_repr _ _ (E :&: E') E)=> //.
  apply/eqP.
  case: setIidPl=> //=.
  apply inter_repr=> //.
Qed.

(** ** Cardinality *)

Lemma fromInt_inj: forall x y,
  fromInt x = fromInt y -> x = y.
Admitted.

Module Int_as_OT <: OrderedType.

  Definition t := Int.

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
  Admitted.

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

Fixpoint pop_tableAux (i: nat) (m: M.t Int) :=
  match i with
  | 0 => M.add zero zero m
  | i'.+1 => M.add (toInt i) (toInt (count_mem true (fromNat (n := tableSize) i))) (pop_tableAux i' m)
  end.

Definition pop_table := pop_tableAux (2 ^ tableSize) (M.empty Int).

Definition pop_elem (bs: Int)(i: nat): Int
  := let x := land (lsr bs (toInt (i * tableSize))) 
                            (dec (lsl one (toInt tableSize))) in
     match (M.find x pop_table) with
     | None => zero
     | Some x => x
     end.

Lemma pop_elem_repr: 
  forall n bs i,
    native_repr n bs ->
    native_repr (pop_elem n i) (cardinal.pop_elem tableSize bs i).
Proof.
  move=> n bs i ?.
  rewrite /pop_elem/cardinal.pop_elem.
  rewrite /cardinal.pop_table.
  rewrite nth_mkseq.
  set i' := land (lsr n (toInt (i * tableSize))) (dec (lsl one (toInt 3))).
  rewrite (M.find_1 (e := toInt (count_mem true (fromNat (n := tableSize) (fromInt i'))))).
  have ->: fromInt i' = toNat (andB (shrBn bs (i * tableSize)) (decB (shlBn # (1) tableSize))).
    rewrite fromInt_def.
    have ->: bitsFromInt i' = andB (shrBn bs (i * tableSize)) (decB (shlBn # (1) tableSize)).
      apply/eqP.
      rewrite -eq_adj.
      admit. (* This should be easy *)
    rewrite //.
  rewrite toInt_def.
  apply/eqIntP=> //.
  rewrite /pop_table /pop_tableAux [_ (2^tableSize) _]/=.
  admit. (* Trivial, but painful *)
  admit. (* toNat (...) < 2 ^ 4: this should be easy *)
Admitted.

Fixpoint popAux (bs: Int)(i: nat): Int :=
  match i with
  | 0 => zero
  | i'.+1 => add (pop_elem bs i') (popAux bs i')
  end.

Definition popAux_repr:
  forall n bs i,
    native_repr n bs ->
    native_repr (popAux n i) (cardinal.popAux tableSize bs i).
Proof.
  move=> n bs i ?.
  elim: i => //=.
  rewrite -fromNat0.
  apply axioms32.zero_repr.
  move=> i IH.
  apply add_repr=> //.
  by apply (pop_elem_repr _ bs).
Qed.

Definition cardinal (bs: Int): Int
  := popAux bs (wordsize %/ tableSize).

Lemma cardinal_repr:
  forall (bs: Int) E, machine_repr bs E ->
    natural_repr (cardinal bs) #|E|.
Proof.
  move=> bs E [bv [int_repr fin_repr]].
  rewrite /natural_repr.
  apply/existsP.
  exists # (#|E|).
  apply/andP; split=> //.
  rewrite - (@cardinal.cardinal_repr _ tableSize bv) => //.
  (* Refold [cardinal], for the proof's sake (and my sanity) *)
  rewrite -[cardinal _]/(popAux bs (wordsize %/ tableSize)).
  rewrite /cardinal.cardinal -[div.divn _ _]/(wordsize %/ tableSize).
  by apply (popAux_repr _ bv).
Qed.

(* TODO: what do we use this one for? *)

Definition ntz (bs: Int): Int
  := add (toInt wordsize) (neg (cardinal (lor bs (neg bs)))).

Lemma ntz_repr:
  forall (bs: Int) x E, machine_repr bs E -> x \in E ->
    natural_repr (ntz bs) [arg min_(k < x in E) k].
Proof.
  move=> bs x E [bv [Hbv1 Hbv2]] Hx.
  rewrite /natural_repr.
  apply/existsP.
  exists #[arg min_(k < x in E) k].
  rewrite -(min.ntz_repr _ bv tableSize)=> //.
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
  apply/eqIntP=> //.
  apply neg_repr.
  move: (cardinal.cardinal_repr _ tableSize (orB bv (negB bv)) E')=> H'.
  rewrite H'.
  have Hok: machine_repr (lor bs (neg bs)) E'.
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