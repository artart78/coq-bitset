From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits extraction.axioms63.

Require Import bineqs repr_op.

Section bloom.

(* Definition *)

Variable P: Type.
Fixpoint bloomSig_aux (T: Int63) (H: seq (P -> 'I_wordsize)) (elem: P): Int63
 := match H with
    | [::] => T
    | h :: t => bloomSig_aux (lor (lsl one (toInt63 (h elem))) T) t elem
    end.

Definition bloomSig (H: seq (P -> 'I_wordsize)) (elem: P): Int63
 := bloomSig_aux zero H elem.

Definition bloomAdd (T: Int63) (H: seq (P -> 'I_wordsize)) (add: P) : Int63
 := lor T (bloomSig H add).

Definition bloomCheck (T: Int63) (H: seq (P -> 'I_wordsize)) (check: P) : bool
 := let sig := bloomSig H check in
    leq (land sig T) sig.

(* Proof *)

Fixpoint bloomSig_repr_aux (T: {set 'I_wordsize}) (H: seq (P -> 'I_wordsize)) (elem: P)
 := match H with
    | [::] => T
    | h :: t => bloomSig_repr_aux ((h elem) |: T) t elem
    end.

Definition bloomSig_repr (H: seq (P -> 'I_wordsize)) (elem: P)
 := bloomSig_repr_aux set0 H elem.

Lemma bloomSig_isRepr:
  forall H T T' add, machine_repr T T' -> machine_repr (bloomSig_aux T H add) (bloomSig_repr_aux T' H add).
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
      rewrite (subset_repr _ _ (bloomSig_repr H check) T') in Habs=> //.
      rewrite /bloomCheck.
      rewrite (subset_repr _ _ (bloomSig_repr H check) (T' :|: (bloomSig_repr H add))).
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
      rewrite (subset_repr _ _ (bloomSig_repr H check) (T' :|: (bloomSig_repr H check))).
      apply subsetUr.
      apply bloomSig_isRepr.
      apply zero_repr.
      apply union_repr=> //.
      apply bloomSig_isRepr.
      apply zero_repr.
    by rewrite Habs' in Hyp.
Qed.

End bloom.

Cd "bloom".

Require Import ExtrOcamlBasic.

Extraction "bloom.ml" bloomAdd bloomCheck.
