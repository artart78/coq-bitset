From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

Require Import ExtrOcamlNatInt.

Require Import repr_op.

Extract Inlined Constant Int63 => "int".

Extract Inlined Constant lsl => "(lsl)".
Extract Inlined Constant lsr => "(lsr)".
Extract Inlined Constant land => "(land)".
Extract Inlined Constant lor => "(lor)".
Extract Inlined Constant lxor => "(lxor)".
Extract Inlined Constant lnot => "lnot".
Extract Inlined Constant ldec => "(fun x -> x - 1)".
Extract Inlined Constant lneg => "-".
Extract Inlined Constant leq => "(=)".
Extract Inlined Constant toInt63 => "".
Extract Inlined Constant fromInt63 => "".

Definition mytest (k: 'I_wordsize) (k': 'I_wordsize): nat :=
  let S := create true in
  get (set S k' false) k.

Set Extraction Optimize.
Set Extraction AutoInline.

Extraction "test.ml" repr_op.create repr_op.get repr_op.set repr_op.inter repr_op.union repr_op.compl repr_op.cardinal repr_op.ntz mytest.
