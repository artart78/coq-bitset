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
   | h :: t => bloomAdd (BitsRepr.lor (BitsRepr.lsl BitsRepr.one (h add)) T) t add
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
  forall H T T' add, native_repr T T' -> native_repr (bloomAdd T H add) (bloomAdd_repr T' H add).
Proof.
  elim=> [//|a l IH] T T' add Hrepr.
  rewrite /bloomAdd /bloomAdd_repr -/bloomAdd -/bloomAdd_repr.
  apply IH.
  apply union_repr=> //.
  apply singleton_repr.
Qed.

Lemma subset_repr: forall (bs bs': BitsRepr.Int63) E E',
  native_repr bs E -> native_repr bs' E' ->
    (BitsRepr.leq (BitsRepr.land bs bs') bs) =
      (E \subset E').
Proof.
  admit.
Admitted.

Lemma bloom_correct1: forall H (T': {set 'I_BitsRepr.wordsize}) add,
  T' \subset bloomAdd_repr T' H add.
Proof.
  elim=> [//=|a l IH T' add].
  apply (subset_trans (B := pred_of_set (a add |: T'))).
  apply subsetU1.
  apply IH.
Qed.

Lemma bloom_correct2': forall H S T S' T' check, native_repr T T' -> native_repr S S' ->
  S' \subset T' ->
  bloomAdd_repr S' H check \subset bloomAdd_repr T' H check.
Proof.
  elim=> [//=|a l IH] S T S' T' check HT HS Hsubset.
  rewrite /bloomAdd_repr -/bloomAdd_repr.
  apply (IH (BitsRepr.lor (BitsRepr.lsl BitsRepr.one (a check)) S)
            (BitsRepr.lor (BitsRepr.lsl BitsRepr.one (a check)) T)).
  apply union_repr=> //.
  apply singleton_repr=> //.
  apply union_repr=> //.
  apply singleton_repr=> //.
  apply setUS=> //.
Qed.  

Lemma bloom_correct2: forall T T' H check, native_repr T T' ->
  bloomCheck (bloomAdd T H check) H check.
Proof.
  move=> T T' H check Hrepr.
  rewrite /bloomCheck.
  rewrite (subset_repr _ _ (bloomAdd_repr set0 H check) (bloomAdd_repr T' H check)).
  apply (bloom_correct2' _ BitsRepr.zero T)=> //.
  apply zero_repr.
  apply sub0set.
  apply bloomAdd_isRepr.
  apply zero_repr.
  apply bloomAdd_isRepr=> //.
Qed.

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
      apply bloom_correct1.
      apply bloomAdd_isRepr=> //.
      apply zero_repr.
      apply bloomAdd_isRepr=> //.
      apply bloomAdd_isRepr=> //.
      apply zero_repr.
    by rewrite Habs' in Hyp.
  * move=> Habs.
    rewrite Habs in Hyp.
    by rewrite (bloom_correct2 _ T') in Hyp.
Qed.