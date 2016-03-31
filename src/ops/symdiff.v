Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Definition symdiff {n} (bs: BITS n) (bs': BITS n): BITS n := xorB bs bs'.

Lemma xorbE : xorb =2 addb.
Proof. by case; case. Qed.

Lemma addbE x y : addb x y = (x && ~~ y) || (~~ x && y).
Proof. by case: x y; case. Qed.

Lemma symdiff_repr n (bs bs' : BITS n) E E' : repr bs E -> repr bs' E' ->
    repr (symdiff bs bs') ((E :\: E') :|: (E' :\: E)).
Proof.
move=> /setP HE /setP HE'; apply/setP=> i; rewrite !inE HE HE' !inE.
by rewrite getBit_liftBinOp // xorbE addbE andbC.
Qed.
