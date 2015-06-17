From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Require Import Omega.

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
