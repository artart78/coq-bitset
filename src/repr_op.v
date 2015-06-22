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

Axiom lnot_repr: forall i bs, repr_op i bs -> repr_op (lnot i) (invB bs).
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
  move=> i E H.
  apply (nat_repr_ax (lnot i) (compl.compl (toBs i))).
  apply lnot_repr.
  apply repr_op_ax.
  apply compl.compl_repr.
  apply repr_ax.
  by apply H.
Qed.

Definition create (b: bool): Int63
  := if b then ldec (toInt63 0) else (toInt63 0).

Lemma create_repr:
  forall (b: bool),
    nat_repr (create b) (if b then [ set : 'I_wordsize ] else set0).
Proof.
  move=> b.
  apply (nat_repr_ax (create b) (create.create b)).
  rewrite /create /create.create.
  case: b.
    apply ldec_repr.
    apply toInt63_repr.
    apply toInt63_repr.
  by apply create.create_repr.
Qed.

Definition get (bs: Int63) (k: 'I_wordsize): bool
  := leq (land (lsr bs k) (toInt63 1)) (toInt63 1).

Lemma get_repr:
  forall i E (k: 'I_wordsize), nat_repr i E ->
    get i k = (k \in E).
Proof.
  move=> i E k H.
  rewrite /get.
  rewrite (leq_repr _ _ (andB (shrBn (toBs i) k) #1) #1).
  apply get.get_repr.
  apply repr_ax=> //.
  apply land_repr.
  apply lsr_repr.
  apply repr_op_ax.
  apply toInt63_repr.
  by apply toInt63_repr.
Qed.

Definition inter (bs: Int63) (bs': Int63): Int63
  := land bs bs'.

Lemma inter_repr:
  forall i i' E E', nat_repr i E -> nat_repr i' E' ->
    nat_repr (inter i i') (E :&: E').
Proof.
  move=> i i' E E' H H'.
  apply (nat_repr_ax (inter i i') (inter.inter (toBs i) (toBs i'))).
  apply land_repr.
  apply repr_op_ax.
  apply repr_op_ax.
  apply inter.inter_repr.
  apply repr_ax=> //.
  by apply repr_ax.
Qed.

Definition keep_min (bs: Int63): Int63
  := land bs (lneg bs).

Lemma keep_min_repr:
  forall i E x, nat_repr i E -> x \in E ->
    nat_repr (keep_min i) [set [arg min_(k < x in E) k]].
Proof.
  move=> i E x H Hx.
  apply (nat_repr_ax (keep_min i) (keep_min.keep_min (toBs i))).
  apply land_repr.
  apply repr_op_ax.
  apply lneg_repr.
  apply repr_op_ax.
  apply keep_min.keep_min_repr=> //.
  by apply repr_ax=> //.
Qed.

Definition set (bs: Int63) k (b: bool): Int63
  := if b then lor bs (lsl (toInt63 1) k) else land bs (lnot (lsl (toInt63 1) k)).

Lemma set_repr:
  forall i (k: 'I_wordsize) (b: bool) E, nat_repr i E ->
    nat_repr (set i k b) (if b then (k |: E) else (E :\ k)).
Proof.
  move=> i k b E H.
  apply (nat_repr_ax (set i k b) (set.set (toBs i) k b)).
  rewrite /set /set.set.
  case: b.
    apply lor_repr.
    apply repr_op_ax.
    apply lsl_repr.
    apply toInt63_repr.
    apply land_repr.
    apply repr_op_ax.
    apply lnot_repr.
    apply lsl_repr.
    apply toInt63_repr.
  apply set.set_repr.
  by apply repr_ax=> //.
Qed.

Definition symdiff (bs: Int63) (bs': Int63): Int63
  := lxor bs bs'.

Lemma symdiff_repr:
  forall i i' E E', nat_repr i E -> nat_repr i' E' ->
    nat_repr (symdiff i i') ((E :\: E') :|: (E' :\: E)).
Proof.
  move=> i i' E E' H H'.
  apply (nat_repr_ax (symdiff i i') (symdiff.symdiff (toBs i) (toBs i'))).
  apply lxor_repr.
  apply repr_op_ax.
  apply repr_op_ax.
  apply symdiff.symdiff_repr.
  apply repr_ax=> //.
  by apply repr_ax.
Qed.

Definition union (bs: Int63) (bs': Int63): Int63
  := lor bs bs'.

Lemma union_repr:
  forall i i' E E', nat_repr i E -> nat_repr i' E' ->
    nat_repr (union i i') (E :|: E').
Proof.
  move=> i i' E E' H H'.
  apply (nat_repr_ax (union i i') (union.union (toBs i) (toBs i'))).
  apply lor_repr.
  apply repr_op_ax.
  apply repr_op_ax.
  apply union.union_repr.
  apply repr_ax=> //.
  by apply repr_ax.
Qed.

(* TODO: cardinal & min *)
