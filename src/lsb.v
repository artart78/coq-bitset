From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

(* Keep only the LSB set to 1 of the number *)

Fixpoint lsb_seq (xs: seq bool): seq bool :=
  match xs with
    | [::] => [::]
    | cons false xs => cons false (lsb_seq xs)
    | cons true xs => cons true (zero (size xs))
  end.

Lemma lsbP {n}(t: BITS n): size (lsb_seq t) == n.
Proof.
  elim: n t=> [t|n IH /tupleP [b t]] //=.
  - (* Case: n ~ 0 *)
    by rewrite (tuple0 t).
  - (* Case: n ~ n.+1 *)
    case: b=> //=.
    + (* Case: b ~ true *)
      by rewrite size_tuple size_nseq.
    + (* Case: b ~ false *)
      by move/eqP: (IH t) => -> //=.
Qed.

Canonical lsb {n} (t: BITS n): BITS n
  := Tuple (lsbP t).

Lemma andB_invB:
  forall n (bs: BITS n),
    andB bs (invB bs) = zero n.
Proof.
  move=> n bs.
  apply allBitsEq.
  move=> k le_k.
  rewrite getBit_liftBinOp; last by assumption.
  rewrite getBit_liftUnOp; last by assumption.
  rewrite andbN -fromNat0 getBit_zero //.
Qed.

Lemma lsb_repr:
  forall n (bs: BITS n),
    andB bs (negB bs) = lsb bs.
Proof.
  elim=> [bs|n IHn /tupleP [b bs]].
  - (* Case: x ~ [tuple] *)
    by apply trivialBits.
  - (* Case: x ~ [tuple b & bs] *)
    case: b.
    + (* Case: b ~ true *)
      have ->: lsb [tuple of true :: bs] = [tuple of true :: (zero n)].
        apply val_inj.
        rewrite /=.
        have ->: (size bs) = n by apply size_tuple.
        by trivial.
      rewrite /negB /incB /invB /andB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons andbT.
      by rewrite -/andB -/invB andB_invB //.
    + (* Case: b ~ false *)
      have ->: lsb [tuple of false :: bs] = [tuple of false :: (lsb bs)]
        by apply val_inj.
      rewrite /negB /incB /invB /andB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite -/incB.
      rewrite liftBinOpCons.
      rewrite andbF.
      rewrite -/andB -/incB -/invB.
      by rewrite IHn //.
Qed.

