From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Require Import bineqs repr_op.

Axiom P: Type.
Definition bloomAdd n (T: BitsRepr.Int63) (H: n.-tuple (P -> 'I_n)) (add: P) : BitsRepr.Int63 :=
  foldr (fun (x: 'I_n) (cur: BitsRepr.Int63) =>
    BitsRepr.lor cur (BitsRepr.lsl BitsRepr.one ((tnth H x) add)))
    T (ord_enum n).

Definition bloomCheck n (T: BitsRepr.Int63) (H: n.-tuple (P -> 'I_n)) (check: P) : bool :=
  let sig := foldr (fun (x: 'I_n) (cur: BitsRepr.Int63) =>
                        BitsRepr.lor cur (BitsRepr.lsl BitsRepr.one ((tnth H x) check)))
                        BitsRepr.zero (ord_enum n) in
  BitsRepr.leq (BitsRepr.land sig T) sig.

Lemma bloom_correct: forall n T H add check,
 (~ bloomCheck n (bloomAdd n T H add) H check) -> (~ bloomCheck n T H check) /\ (add <> check).
Proof.
  move=> n T H add check Hyp.
  split.
  * move=> Habs.
    have Habs': bloomCheck n (bloomAdd n T H add) H check.
      rewrite /bloomCheck.
      admit.
    by rewrite Habs' in Hyp.
  * move=> Habs.
    rewrite Habs in Hyp.
    have Habs': bloomCheck n (bloomAdd n T H check) H check.
      admit.
    by rewrite Habs' in Hyp.
Admitted.