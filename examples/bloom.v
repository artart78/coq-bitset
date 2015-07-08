From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Require Import bineqs repr_op.

(* Definition *)

Axiom P: Type.
Fixpoint bloomAdd (T: BitsRepr.Int63) (H: seq (P -> 'I_BitsRepr.wordsize)) (add: P) : BitsRepr.Int63
 := match H with
   | [::] => T
   | h :: t => bloomAdd (BitsRepr.lor T (BitsRepr.lsl BitsRepr.one (h add))) t add
   end.

Definition bloomCheck (T: BitsRepr.Int63) (H: seq (P -> 'I_BitsRepr.wordsize)) (check: P) : bool
 := let sig := bloomAdd BitsRepr.zero H check in
    BitsRepr.leq (BitsRepr.land sig T) sig.

(* Proof *)

Fixpoint bloomAdd_repr (T: {set 'I_BitsRepr.wordsize}) (H: seq (P -> 'I_BitsRepr.wordsize)) (add: P)
 := match H with
    | [::] => T
    | h :: t => bloomAdd_repr ((h add) |: T) t add
    end.

Lemma bloomAdd_isRepr:
  forall T T' H add, native_repr T T' -> native_repr (bloomAdd T H add) (bloomAdd_repr T' H add).
Proof.
  admit.
Admitted.

Lemma subset_repr: forall (bs bs': BitsRepr.Int63) E E',
  native_repr bs E -> native_repr bs' E' ->
    (BitsRepr.leq (BitsRepr.land bs bs') bs) =
      (E \subset E').
Proof.
  admit.
Admitted.

Lemma bloom_correct1: forall T T' H add, native_repr T T' ->
  T' \subset bloomAdd_repr T' H add.
Proof.
  admit.
Admitted.

Lemma bloom_correct2: forall T H check,
  bloomCheck (bloomAdd T H check) H check.
Proof.
  admit.
Admitted.

Lemma bloom_correct: forall T T' H add check, native_repr T T' ->
 (~ bloomCheck (bloomAdd T H add) H check) -> (~ bloomCheck T H check) /\ (add <> check).
Proof.
  move=> T T' H add check Hrepr Hyp.
  split.
  * move=> Habs.
    have Habs': bloomCheck (bloomAdd T H add) H check.
      rewrite /bloomCheck in Habs.
      rewrite (subset_repr _ _ (bloomAdd_repr set0 H check) T') in Habs=> //.
      rewrite /bloomCheck.
      rewrite (subset_repr _ _ (bloomAdd_repr set0 H check) (bloomAdd_repr T' H add)).
      rewrite (subset_trans (B := pred_of_set T')) //.
      apply (bloom_correct1 T)=> //.
      apply bloomAdd_isRepr=> //.
      apply zero_repr.
      apply bloomAdd_isRepr=> //.
      apply bloomAdd_isRepr=> //.
      apply zero_repr.
    by rewrite Habs' in Hyp.
  * move=> Habs.
    rewrite Habs in Hyp.
    by rewrite bloom_correct2 in Hyp.
Qed.