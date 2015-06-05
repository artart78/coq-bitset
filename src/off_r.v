From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Fixpoint off_r_seq (xs: seq bool): seq bool :=
  match xs with
    | [::] => [::]
    | cons false xs => cons false (off_r_seq xs)
    | cons true xs => cons false xs
  end.

(** We then prove some invariant on the size of the resulting list. *)
Lemma off_rP {n}(t: BITS n): size (off_r_seq t) == n.
Proof.
  elim: n t=> [t|n IH /tupleP [b t]] //=.
  - (* Case: n ~ 0 *)
    by rewrite (tuple0 t).
  - (* Case: n ~ n.+1 *)
    case: b=> //=.
    + (* Case: b ~ true *)
      by rewrite size_tuple.
    + (* Case: b ~ false *)
      move/eqP: (IH t) => -> //=.
Qed.

(** We conclude with a canonical structure lifting the list-level
operation to (dependently-typed) tuples. *)
Canonical off_r {n} (t: BITS n): BITS n
  := Tuple (off_rP t).

(** 

  This example turns off the leftmost bit in a bitvector. This is
  trivial to prove, but (slightly) less so to specify: we must write a
  genuine program over the list of bits.

 *)

Lemma off_r_repr:
  forall n (bs: BITS n),
    andB bs (subB bs #1) = off_r bs.
Proof.
  elim=> [bs|n IHn /tupleP [b bs]].
  - (* Case: x ~ [tuple] *)
    by apply trivialBits.
  - (* Case: x ~ [tuple b & bs] *)
    case: b.
    + (* Case: b ~ true *)
      have ->: off_r [tuple of true :: bs] = [tuple of false :: bs]
        by apply: val_inj.
      by rewrite subB1 /= tuple.beheadCons
                 /andB liftBinOpCons -/andB andBB.
    + (* Case: b ~ false *)
      have ->: off_r [tuple of false :: bs] = [tuple of false :: off_r bs]
        by apply: val_inj.
      by rewrite subB1 /= tuple.beheadCons -subB1
                 /andB liftBinOpCons -/andB IHn.
Qed.

