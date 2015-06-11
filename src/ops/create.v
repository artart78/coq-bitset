From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg finset.
From Bits
     Require Import bits.
Require Import props.bineqs props.getbit spec.

Definition create {n} (b: bool): BITS n
  := if b then dropmsb (subB (shlBn (n := n.+1) #1 n) #1) else #0.

Lemma create_repr:
  forall n (b: bool), n > 0 ->
    repr (create b) (if b then [ set : 'I_n ] else set0).
Proof.
  move=> n b gtz_n.
  rewrite /repr -setP /eq_mem=> x.
  rewrite !fun_if !in_set !if_arg.
  rewrite -makeOnes dropmsb_joinmsb getBit_zero=> //.
  rewrite getBit_ones=> //.
  by case: b=> //.
Qed.
