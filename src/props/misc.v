From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.

Lemma count_true:
  forall n, (count_mem true (nseq n true)) = n.
Proof.
  elim=> //=.
  auto with arith.
Qed.

