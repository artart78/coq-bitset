From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

Require Import ExtrOcamlNatInt.

Require Import repr_op.


Definition mytest (k: 'I_BitsRepr.wordsize) (k': 'I_BitsRepr.wordsize): nat :=
  let S := create true in
  get (set S k' false) k.

Set Extraction Optimize.
Set Extraction AutoInline.

Extraction "test.ml" repr_op.create repr_op.get repr_op.set repr_op.inter repr_op.union repr_op.compl repr_op.cardinal repr_op.ntz mytest.
