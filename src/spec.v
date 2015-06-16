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
  rewrite in_set HE !in_set.
  rewrite /getBit inordK.
  rewrite -nth_behead //=.
  rewrite -[i.+1]addn1 -[n.+1]addn1.
  rewrite ltn_add2r.
  by apply ltn_ord.
Qed.
