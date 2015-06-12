From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Definition repr {n}(bs: BITS n) E :=
  E = [ set x : 'I_n | getBit bs x ].

Lemma repr_rec:
  forall n (bs: BITS n) E b, repr [tuple of b :: bs] E ->
    repr bs [ set x : 'I_n | inord(x.+1) \in E ].
Proof.
  move=> n bs E b.
  rewrite !/repr -!setP !/eq_mem=> HE.
  move=> i.
  rewrite in_set.
  rewrite HE.
  rewrite !in_set.
  rewrite /getBit.
  rewrite inordK.
  rewrite -nth_behead.
  rewrite //=.
  admit. (* Trivial... *)
Admitted.
