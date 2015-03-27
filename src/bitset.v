From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require get.

Parameter wordsize: nat.

Definition SET := BITS wordsize.


Definition get (S: SET)(k: 'I_wordsize): SET 
  := get.get S k.