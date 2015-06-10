From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.
Require Import props.bineqs.

Definition create {n} (b: bool): BITS n
  := if b then dropmsb (subB (shlBn (n := n.+1) #1 n) #1) else #0.

Lemma create_repr:
  forall n (b: bool), n > 0 ->
    create b = if b then ones n else spec.zero n.
Proof.
  move=> n b gtz_n.
  have ->: ones n = dropmsb (joinmsb (false, ones n)) by rewrite dropmsb_joinmsb.
  rewrite makeOnes /create fromNat0 //.
Qed.
