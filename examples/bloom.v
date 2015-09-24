From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits extraction.axioms63.

Require Import bineqs repr_op.

Section bloom.

(* Definition *)

Variable P: Type.

Section bloom_def.

Variable T: Type.
Variable union: T -> T -> T. (* lor, |: *)
Variable singleton: nat -> T. (* x -> lsl one (toInt63 x), id *)
Variable empty: T.

Fixpoint bloomSig_def_aux (curFilter: T) (H: seq (P -> 'I_wordsize)) (elem: P): T
 := match H with
    | [::] => curFilter
    | h :: t => bloomSig_def_aux (union (singleton (h elem)) curFilter) t elem
    end.

Definition bloomSig_def (H: seq (P -> 'I_wordsize)) (elem: P): T
 := bloomSig_def_aux empty H elem.

End bloom_def.

Definition bloomSig
 := bloomSig_def Int63 lor (fun x => lsl one (toInt63 x)) zero.
Definition bloomSig_aux
 := bloomSig_def_aux Int63 lor (fun x => lsl one (toInt63 x)).

Definition bloomSig_repr
 := bloomSig_def {set 'I_wordsize} (setU (T := ordinal_finType wordsize)) (fun x => [set (inord x)]) set0.
Definition bloomSig_repr_aux
 := bloomSig_def_aux {set 'I_wordsize} (setU (T := ordinal_finType wordsize)) (fun x => [set (inord x)]).

Definition bloomAdd (T: Int63) (H: seq (P -> 'I_wordsize)) (add: P) : Int63
 := lor T (bloomSig H add).

Definition bloomCheck (T: Int63) (H: seq (P -> 'I_wordsize)) (check: P) : bool
 := let sig := bloomSig H check in
    leq (land sig T) sig.

(* Proof *)

Lemma bloomSig_isRepr:
  forall H T T' add, machine_repr T T' -> machine_repr (bloomSig_aux T H add) (bloomSig_repr_aux T' H add).
Proof.
  elim=> [//|a l IH] T T' add Hrepr.
  rewrite /bloomSig /bloomSig_repr -/bloomSig -/bloomSig_repr.
  apply IH.
  apply union_repr=> //.
  have {1}->: a add = inord (n' := wordsize.-1) (a add).
    apply ord_inj.
    by rewrite inordK.
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
