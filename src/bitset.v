From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

Parameter wordsize: nat.

Definition Word := BITS wordsize.
Definition SET := Word.

Require get.
Definition get (S: SET)(k: 'I_wordsize): SET 
  := get.get S k.

Definition set (S: SET)(k: 'I_wordsize)(b: bool): SET.
Admitted.

Definition inter (S1 S2: SET): SET.
Admitted.

Definition union (S1 S2: SET): SET.
Admitted.

Definition compl (S: SET): SET.
Admitted.

Definition diag (S1 S2: SET): SET.
Admitted.

(* TODO: Refine typing of [i], [n] and [j] *)
Definition blit (S1: SET)(i n: nat)(S2: SET)(j: nat): SET.
Admitted.

(* TODO: Refine typing of [i] and [n] *)
Definition subset (S1: SET)(i n: nat): SET.
Admitted.

(* TODO: Refine typing of [i] and [n] *)
Definition fill (S1: SET)(i n: nat)(b: bool): SET.
Admitted.

(* TODO: Is [k] consuming 'I_wordsize or a (less-precisely typed)
[Word] *) 
Definition iteri {A}(S: SET)(k: 'I_wordsize -> A -> A)(bc:
A): A.
Admitted.

Definition cardinal (S: SET): Word.
Admitted.
