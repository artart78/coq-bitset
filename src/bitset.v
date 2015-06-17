From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

Parameter bytesize: nat.
Parameter wordsize: nat.

Definition Word := BITS wordsize.
Definition SET := Word.

Require create get set inter union symdiff compl cardinal.

Definition create (b: bool): SET
  := create.create b.

Definition get (S: SET)(k: 'I_wordsize): bool
  := get.get S k.

Definition set (S: SET)(k: 'I_wordsize)(b: bool): SET
  := set.set S k b.

Definition inter (S1 S2: SET): SET
  := inter.inter S1 S2.

Definition union (S1 S2: SET): SET
  := union.union S1 S2.

Definition symdiff (S1 S2: SET): SET
  := symdiff.symdiff S1 S2.

Definition compl (S: SET): SET
  := compl.compl S.

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

Definition cardinal (S: SET): nat
  := cardinal.cardinal bytesize S.
