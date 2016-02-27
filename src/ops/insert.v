Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Definition insert {n}(bs: BITS n) k: BITS n := orB bs (shlBn #1 k).

Lemma insert_repr: forall n (bs: BITS n) (k: 'I_n) E, repr bs E ->
    repr (insert bs k) (k |: E).
Proof.
  move=> n bs k E HE.
  rewrite /repr -setP /eq_mem=> x.
  rewrite in_set getBit_set_true=> //.
  rewrite fun_if.
  case H: (x == k).
    + (* Case: x == k *)
      move/eqP: H ->.
      by rewrite eq_refl setU11.
    + (* Case: x <> k *)
      rewrite ifF=> //.
      by rewrite in_setU1 H HE in_set.
Qed.
