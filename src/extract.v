From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

Require Import ExtrOcamlNatInt.

Require Import bitset.

Extract Constant wordsize => "63".
Extract Constant BITS => "int".

(* TODO: check that n <= 63 *)
Extract Constant shrBn => "fun n p k -> p lsr k".
Extract Constant shlBn => "fun n p k -> p lsl k".
(* TODO: It would have been better to replace subB; here, we should ensure that b != false *)
Extract Constant sbbB => "fun n b p1 p2 -> (0, p1 - p2)".
Extract Constant andB => "fun n p1 p2 -> p1 land p2".
Extract Constant orB => "fun n p1 p2 -> p1 lor p2".
Extract Constant invB => "fun n p -> lnot p".
(* TODO: check that the highest bit is 0 *)
Extract Constant dropmsb => "fun n p -> p".
Extract Constant fromNat => "fun n p -> p".
Extract Inlined Constant eq_op => "(fun t x y -> x = y)".

Definition mytest (k: 'I_wordsize) (k': 'I_wordsize): nat :=
  let S := create true in
  get (set S k' false) k.

Set Extraction Optimize.
Set Extraction AutoInline.

Extraction "test.ml" mytest.