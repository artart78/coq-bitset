From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun.
From MathComp
     Require Import tuple finset.
From Bits
     Require Import bits extraction.axioms32.

Require Import bineqs repr_op.

(* Definition *)

Variable P: Type.

Module bloom_def (S: SET).
Import S.

Fixpoint bloomSig_aux (curFilter: T) (H: seq (P -> 'I_wordsize)) (elem: P): T
 := match H with
    | [::] => curFilter
    | h :: t => bloomSig_aux ((singleton (h elem)) \cup curFilter) t elem
    end.

Definition bloomSig (H: seq (P -> 'I_wordsize)) (elem: P): T
 := bloomSig_aux \emptyset H elem.

Definition bloomAdd (S: T) (H: seq (P -> 'I_wordsize)) (add_elt: P) : T
 := S \cup (bloomSig H add_elt).

Definition bloomCheck (S: T) (H: seq (P -> 'I_wordsize)) (checked_elt: P) : bool
 := let sig := bloomSig H checked_elt in
    (sig \cap S) = sig.

End bloom_def.

Bind Scope SET_scope with Int.
Module bloom_Int := bloom_def Bitset.
Export bloom_Int.
Module bloom_Finset := bloom_def Finset.

Definition bloomSig_repr := bloom_Finset.bloomSig.
Definition bloomSig_aux_repr := bloom_Finset.bloomSig_aux.

(* Proof *)

Lemma bloomSig_isRepr:
  forall H T T' add, machine_repr T T' -> machine_repr (bloomSig_aux T H add) (bloomSig_aux_repr T' H add).
Proof.
  elim=> [//|a l IH] T T' add Hrepr.
  rewrite /bloomSig /bloomSig_repr -/bloomSig -/bloomSig_repr.
  apply IH.
  apply union_repr=> //.
  apply singleton_repr.
Qed.

Lemma bloom_correct: forall T T' H add check, machine_repr T T' ->
 (~ bloomCheck (bloomAdd T H add) H check) -> (~ bloomCheck T H check) /\ (add <> check).
Proof.
  move=> T T' H add check Hrepr Hyp.
  split.
  * move=> Habs.
    have Habs': bloomCheck (bloomAdd T H add) H check.
      rewrite /bloomCheck in Habs.
      rewrite /Bitset.eq (subset_repr _ _ (bloomSig_repr H check) T') in Habs=> //.
      rewrite /bloomCheck.
      rewrite /Bitset.eq (subset_repr _ _ (bloomSig_repr H check) (T' :|: (bloomSig_repr H add))).
      rewrite (subset_trans (B := pred_of_set T')) //.
      apply subsetUl.
      apply bloomSig_isRepr.
      apply zero_repr.
      apply union_repr=> //.
      apply bloomSig_isRepr.
      apply zero_repr.
      apply bloomSig_isRepr.
      apply zero_repr.
    by rewrite Habs' in Hyp.
  * move=> Habs.
    rewrite Habs in Hyp.
    have Habs': bloomCheck (bloomAdd T H check) H check.
      rewrite /bloomCheck.
      rewrite /Bitset.eq (subset_repr _ _ (bloomSig_repr H check) (T' :|: (bloomSig_repr H check))).
      apply subsetUr.
      apply bloomSig_isRepr.
      apply zero_repr.
      apply union_repr=> //.
      apply bloomSig_isRepr.
      apply zero_repr.
    by rewrite Habs' in Hyp.
Qed.

Cd "bloom".

Require Import ExtrOcamlBasic.

Extraction "bloom.ml" bloomAdd bloomCheck.
