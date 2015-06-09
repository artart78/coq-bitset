From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div.
From Bits
     Require Import bits.
Require Import props cardinal.

(* Fill all the bits to 1 after the LSB *)

Fixpoint fill_ntz_seq (xs: seq bool): seq bool :=
  match xs with
    | [::] => [::]
    | cons false xs => cons false (fill_ntz_seq xs)
    | cons true xs => cons true (ones (size xs))
  end.

Lemma fill_ntzP {n}(t: BITS n): size (fill_ntz_seq t) == n.
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

Canonical fill_ntz {n} (t: BITS n): BITS n
  := Tuple (fill_ntzP t).

Lemma orB_invB:
  forall n (bs: BITS n),
    orB bs (invB bs) = ones n.
Proof.
  move=> n bs.
  apply allBitsEq=> k le_k.
  rewrite getBit_liftBinOp; last by assumption.
  rewrite getBit_liftUnOp; last by assumption.
  rewrite orbN /getBit nth_nseq le_k //.
Qed.
  
Lemma fill_ntz_repr:
  forall n (bs: BITS n),
    orB bs (negB bs) = fill_ntz bs.
Proof.
  elim=> [bs|n IHn /tupleP [b bs]].
  - (* Case: x ~ [tuple] *)
    by apply trivialBits.
  - (* Case: x ~ [tuple b & bs] *)
    case: b.
    + (* Case: b ~ true *)
      have ->: fill_ntz [tuple of true :: bs] = [tuple of true :: (ones n)].
        apply val_inj.
        by rewrite /= size_tuple //.
      rewrite /negB /incB /invB /orB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons orbT.
      by rewrite -/orB -/invB orB_invB //.
    + (* Case: b ~ false *)
      have ->: fill_ntz [tuple of false :: bs] = [tuple of false :: (fill_ntz bs)]
        by apply val_inj.
      rewrite /negB /incB /invB /orB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons orbF.
      by rewrite -/orB IHn.
Qed.

Definition ntz {n}(k: nat)(bs: BITS n): nat := n - (cardinal k (orB bs (negB bs))).

Lemma count_true:
  forall n, (count_mem true (nseq n true)) = n.
Proof.
  elim=> //=.
  auto with arith.
Qed.

Lemma ntz_repr:
  forall n (bs: BITS n) k,
    ntz k bs = index true bs.
Proof.
  move=> n bs k.
  rewrite /ntz cardinal_repr.
  rewrite fill_ntz_repr.
  elim: n bs=> [bs|n IHn /tupleP[b bs]].
  + (* n ~ 0 *)
    by rewrite tuple0 [bs]tuple0.
  + (* n ~ n.+1 *)
    case: b.
    - (* b ~ true *)
      have ->: fill_ntz [tuple of true :: bs] = [tuple of true :: ones n].
        apply val_inj.
        by rewrite /= size_tuple //.
      rewrite /=.
      rewrite count_true.
      by rewrite addnC addn1 subnn.
    - (* b ~ false *)
      have ->: fill_ntz [tuple of false :: bs] = [tuple of false :: (fill_ntz bs)]
        by apply val_inj.
      rewrite /=.
      rewrite /= -IHn.
      rewrite add0n subSn //.
      have {2}->: n = size (fill_ntz_seq bs).
        have H: size (fill_ntz_seq bs) == n by apply fill_ntzP.
        move/eqP: H=>H.
        by rewrite H //.
      apply count_size.
      admit. (* TODO: only enable the case when 2 ^ k %| n *)
Admitted.
