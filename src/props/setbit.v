From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div ssralg.
From Bits
     Require Import bits.
Require Import props.

Lemma setBit_0:
  forall n, setBit (n := n) #0 0 true = #1.
Proof.
  case=> // n.
  + (* n ~ n + 1 *)
    by rewrite //= tuple.beheadCons.
Qed.

Lemma dropmsb_setBit:
  forall n k, k < n ->
    (dropmsb (setBit (n := n.+1) #0 k true) = setBit (n := n) #0 k true).
Proof.
  elim=> // n IHn k le_k.
  elim: k le_k=> [|k IHk le_k].
  + (* k ~ 0 *)
    rewrite /= !tuple.beheadCons /= dropmsb_joinlsb /dropmsb splitmsb_0 //=.
  + (* k ~ k + 1 *)
    rewrite {1}/setBit /setBitAux -/setBitAux !splitlsb_0.
    (* TODO: copying a large chunk of code is not esthetically
       pleasing (nor future-proof). Is there a way to proceed
       otherwise, by unfolding setBit and setBitAux on the right-hand
       side, instead of folding the left-hand side? *)
    have ->:
        (match k with
         | 0 => joinlsb (n := n) (# (0), true)
         | i'.+1 => joinlsb (setBitAux i' true # (0), false)
         end) = setBitAux k true #0.
      by rewrite {2}/setBitAux /= tuple.beheadCons tuple.theadCons /=
                 -/setBitAux //.
    have ->: setBitAux k true #0 = setBit #0 k true. by trivial.
    rewrite dropmsb_joinlsb IHn.
    rewrite {2}/setBit /setBitAux splitlsb_0 //.
    by apply le_k.
Qed.

