Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Definition remove {n}(bs: BITS n) k: BITS n
  := andB bs (invB (shlBn #1 k)).

Lemma remove_repr:
  forall n (bs: BITS n) (k: 'I_n) E, repr bs E ->
    repr (remove bs k) (E :\ k).
Proof.
  move=> n bs k E HE.
  rewrite /repr -setP /eq_mem=> x.
  rewrite in_set getBit_set_false=> //.
  rewrite fun_if.
  case H: (x == k).
    + (* Case: x == k *)
      move/eqP: H ->.
      rewrite ifT=> //.
      by rewrite setD11.
    + (* Case: x <> k *)
      rewrite ifF=> //.
      by rewrite in_setD1 H HE in_set.
Qed.
