From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import props.getbit spec.

Definition set {n}(bs: BITS n) k (b: bool): BITS n
  := if b then orB bs (shlBn #1 k) else andB bs (invB (shlBn #1 k)).

Lemma set_repr:
  forall n (bs: BITS n) (k: 'I_n) (b: bool) E, repr bs E ->
    repr (set bs k b) (if b then (k |: E) else (E :\ k)).
Proof.
  move=> n bs k b E HE.
  rewrite /repr.
  rewrite -setP /eq_mem=> x.
  rewrite in_set [getBit _]fun_if if_arg.
  rewrite getBit_set_true=> //.
  rewrite getBit_set_false=> //.
  case H: (x == k).
    + (* Case: x == k *)
      move/eqP: H=> ->.
      rewrite !fun_if !if_arg.
      rewrite ![if k == k then _ else _]ifT=> //.
      rewrite setU11 setD11.
      by case: b=> //.
    + (* Case: x <> k *)
      rewrite !fun_if !if_arg.
      rewrite ![if x == k then _ else _]ifF=> //.
      rewrite in_setU1 in_setD1 H HE in_set.
      by case: b=> //.
Qed.