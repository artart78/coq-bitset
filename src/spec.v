From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import props.getbit.

Definition repr {n}(bs: BITS n) E :=
  E = [ set x : 'I_n | getBit bs x ].

Lemma repr_rec:
  forall n (bs: BITS n) E b, repr [tuple of b :: bs] E ->
    repr bs [ set x : 'I_n | inord(x.+1) \in E ].
Proof.
  move=> n bs E b.
  rewrite !/repr -!setP !/eq_mem=> HE i.
  rewrite in_set HE !in_set inordK.
  rewrite /getBit -nth_behead //=.
  have ltn_i: i < n by apply ltn_ord.
  by auto with arith.
Qed.

Lemma singleton_repr:
  forall n (k: 'I_n), repr (setBit #0 k true) [set k].
Proof.
  move=> n k.
  rewrite /repr -setP /eq_mem=> x.
  rewrite !in_set.
  case x_eq_k: (x == k).
  + (* x == k *)
    move/eqP: x_eq_k ->.
    by rewrite setBitThenGetSame.
  + (* x <> k *)
    rewrite setBitThenGetDistinct=> //.
    rewrite getBit_zero //.
    apply not_eq_sym.
    move=> x_is_k.
    move/eqP: x_eq_k=>x_eq_k.
    apply x_eq_k.
    by apply ord_inj.
Qed.
