From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import bitset spec.

Axiom Int63: Type.
Definition wordsize := 63.

Axiom repr_op: Int63 -> (BITS wordsize) -> Prop.
Axiom nat_repr: Int63 -> {set ordinal_finType wordsize} -> Prop.
Axiom nat_repr_ax: forall i bs E, repr_op i bs -> repr bs E -> nat_repr i E.
Axiom toBs: Int63 -> BITS wordsize.
Axiom repr_ax: forall i E, nat_repr i E -> repr (toBs i) E.
Axiom repr_op_ax: forall i, repr_op i (toBs i).

Axiom lnot: Int63 -> Int63.
Axiom land: Int63 -> Int63 -> Int63.
Axiom lor: Int63 -> Int63 -> Int63.
Axiom lxor: Int63 -> Int63 -> Int63.
Axiom lsr: Int63 -> nat -> Int63.
Axiom lsl: Int63 -> nat -> Int63.
Axiom lneg: Int63 -> Int63.
Axiom ldec: Int63 -> Int63.
Axiom leq: Int63 -> Int63 -> bool.
Axiom toInt63: nat -> Int63.

Axiom lnot_repr: forall i bs, repr_op i bs -> repr_op (lnot i) (negB bs).
Axiom land_repr: forall i i' bs bs', repr_op i bs -> repr_op i' bs' -> repr_op (land i i') (andB bs bs').
Axiom lor_repr: forall i i' bs bs', repr_op i bs -> repr_op i' bs' -> repr_op (lor i i') (orB bs bs').
Axiom lxor_repr: forall i i' bs bs', repr_op i bs -> repr_op i' bs' -> repr_op (lxor i i') (xorB bs bs').
Axiom lsr_repr: forall i bs k, repr_op i bs -> repr_op (lsr i k) (shrBn bs k).
Axiom lsl_repr: forall i bs k, repr_op i bs -> repr_op (lsl i k) (shlBn bs k).
Axiom lneg_repr: forall i bs, repr_op i bs -> repr_op (lneg i) (negB bs).
Axiom ldec_repr: forall i bs, repr_op i bs -> repr_op (ldec i) (decB bs).
Axiom leq_repr: forall i i' bs bs', repr_op i bs -> repr_op i' bs' -> (leq i i') = (bs == bs').
Axiom toInt63_repr: forall k, repr_op (toInt63 k) #k.

Definition compl (bs: Int63): Int63
  := lnot bs.

Lemma compl_repr:
  forall i E, nat_repr i E -> nat_repr (lnot i) (~: E).
Proof.
  admit.
Admitted.

Definition create (b: bool): Int63
  := if b then ldec (toInt63 0) else (toInt63 0).

Definition get (bs: Int63) (k: 'I_wordsize): bool
  := leq (land (lsr bs k) (toInt63 1)) (toInt63 1).

Definition inter (bs: Int63) (bs': Int63): Int63
  := land bs bs'.

Definition keep_min (bs: Int63): Int63
  := land bs (lneg bs).

Definition set (bs: Int63) k (b: bool): Int63
  := if b then lor bs (lsr (toInt63 1) k) else land bs (lnot (lsr (toInt63 1) k)).

Definition symdiff (bs: Int63) (bs': Int63): Int63
  := lxor bs bs'.

Definition union (bs: Int63) (bs': Int63): Int63
  := lor bs bs'.
