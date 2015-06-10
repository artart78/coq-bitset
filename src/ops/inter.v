From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import props.getbit spec.

Definition inter {n} (bs: BITS n) (bs': BITS n): BITS n
  := andB bs bs'.

Lemma inter_repr:
  forall n (bs: BITS n) (bs': BITS n) E E', repr bs E -> repr bs' E' ->
    repr (inter bs bs') (E :&: E').
Proof.
  move=> n bs bs' E E' HE HE'.
  rewrite /repr.
  rewrite -setP /eq_mem=> x.
  rewrite in_setI /inter /andB HE HE' !in_set getBit_liftBinOp //.
Qed.
