Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits extraction.axioms32.
From CoqEAL
     Require Import hrel param refinements.
Import Refinements.Op.
Require Import bineqs repr_op spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Definition *)

(* Unset Universe Polymorphism. *)
(* Set Universe Polymorphism.  *)
Section Bloom_generic.

Variables (Finset : Type)
          (P: Type)
          (I : Type).

(* Realizer P as P_R := ?. *)

Context `{eq_of Finset}.
Context `{union_of Finset}.
Context `{inter_of Finset}.
Context `{singleton_of I Finset}.
Context `{emptyset_of Finset}.

Fixpoint bloomSig_aux (H: seq (P -> I))(e: P)(curFilter: Finset): Finset
 := match H with
    | [::] => curFilter
    | h :: H => bloomSig_aux H e (union_op (singleton_op (h e)) curFilter) 
    end.

Definition bloomSig (H: seq (P -> I))(e: P): Finset
 := bloomSig_aux H e emptyset_op.

Definition bloomAdd (H: seq (P -> I))(add_elt: P)(S: Finset): Finset
 := union_op S (bloomSig H add_elt).

Definition bloomCheck (H: seq (P -> I))(e: P)(S: Finset) : bool
 := let sig := bloomSig H e in ((inter_op sig S) == sig)%C.

End Bloom_generic.


Parametricity bloomSig_aux.


Parameter Q : Type.

Local Instance refl_Q (x : Q) : refines Logic.eq x x.
rewrite refinesE //.
Qed.


Local Instance refl_seqH (x : seq (Q -> 'I_wordsize)) : refines (list_R (Logic.eq ==> Logic.eq)%rel) x x.
rewrite refinesE //.
elim x=> //=; constructor=> //.
move=> u v -> //.
Qed.

Lemma bloomSig_isRepr (H : seq (Q -> 'I_wordsize))(e : Q) : 
  refines (@Rfin wordsize ==> Rfin)%rel (bloomSig_aux H e) (bloomSig_aux H e).
Proof.
  rewrite refinesE.
  move=> f1 f2 R.
  eapply bloomSig_aux_R with (P_R := Logic.eq)=> //;
  move=> *; apply refinesP; do?eapply refines_apply; tc.
Qed.

Lemma bloom_correct: forall (H : seq (Q -> 'I_wordsize))(add check : Q)(fset: {set 'I_wordsize}), 
  (~ bloomCheck H check  (bloomAdd H add fset)) ->
    (~ bloomCheck H check fset) /\ (add <> check).
Proof.
  Local Arguments inter_op /.
  Local Arguments inter.inter_Finset /.
  Local Arguments union_op /.
  Local Arguments union.union_Finset /.

  move=> H add check T Hyp.
  split.
  * move=> Habs.
    rewrite /bloomCheck in Habs.
    apply Hyp.
    rewrite /bloomCheck/bloomAdd.
    rewrite /= setIUr.
    rewrite /= in Habs.
    move/eqP: Habs => ->.
    simpC.
    apply/eqP/setUidPl.
    apply subsetIl.
  * move=> Habs.
    rewrite Habs in Hyp.
    apply Hyp.
    have Habs': bloomCheck  H check (bloomAdd H check T).
    rewrite /bloomCheck.
    simpC. rewrite /=.
    apply/eqP.
    
      rewrite /Bitset.eq (subset_repr _ _ (bloomSig_repr H check) (T' :|: (bloomSig_repr H check))).
      apply subsetUr.
      apply bloomSig_isRepr.
      apply zero_repr.
      apply union_repr=> //.
      apply bloomSig_isRepr.
      apply zero_repr.
    by rewrite Habs' in Hyp.
Qed.

(* TODO: translate high-level spec [bloom_correct] onto bit-level implementation *)

Cd "examples/bloom".

Require Import ExtrOcamlBasic.

Extraction "bloom.ml" bloomAdd bloomCheck.

Cd "../..".
