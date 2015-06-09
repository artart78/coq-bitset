From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import props.

Definition get {n}(bs: BITS n)(k: 'I_n): BITS n
  := andB (shrBn bs k) #1.

Lemma get_repr:
  forall n (k: 'I_n)(bs: BITS n), 
    get bs k = (if getBit bs k then #1 else #0).
Proof.
  move=> n k S.
  by rewrite /get andB_mask1 getBit_shrBn.
Qed.
