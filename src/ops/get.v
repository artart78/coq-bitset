From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun.
From MathComp
     Require Import tuple finset.
From Bits
     Require Import bits.
Require Import props.bineqs props.getbit spec.

Definition get {n}(bs: BITS n)(k: 'I_n): bool
  := (andB (shrBn bs k) #1) == #1.

Lemma get_repr:
  forall n (k: 'I_n.+1)(bs: BITS n.+1) E, repr bs E ->
    get bs k = (k \in E).
Proof.
  move=> n k bs E HE.
  rewrite /get andB_mask1 getBit_shrBn addn0=> //.
  rewrite HE in_set.
  case: (getBit bs k).
  + (* getBit bs k = true *)
    by rewrite eq_refl.
  + (* getBit bs k = false *)
    by case H: (#0 == #1)=> //.
Qed.
