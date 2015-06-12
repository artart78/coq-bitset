From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div finset.
From Bits
     Require Import bits.
Require Import props.bineqs props.misc cardinal spec.

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

Lemma repr_rec:
  forall n (bs: BITS n) E b, repr [tuple of b :: bs] E ->
    repr bs [ set x : 'I_n | inord(x.+1) \in E ].
Proof.
  admit.
Admitted.

Lemma ntz_repr:
  forall n (bs: BITS n) k x E, repr bs E -> x \in E ->
    ntz k bs = [arg min_(k < x in E) k].
Proof.
  move=> n bs k x E HE Hx.
  case: arg_minP.
  apply Hx.
  move=> i Hi Hj.
  rewrite /ntz.
  rewrite fill_ntz_repr.
  set ntzE := [ set x : 'I_n | getBit (fill_ntz bs) x ].
  have H: repr (fill_ntz bs) ntzE=> //.
  rewrite (cardinal_repr n k (fill_ntz bs) ntzE)=> //.
  rewrite -(count_repr n (fill_ntz bs) ntzE)=> //.
  elim: n bs x E HE Hx i Hi Hj ntzE H=> [bs|n IHn /tupleP[b bs]] x E HE Hx i Hi Hj ntzE H.
  + (* n ~ 0 *)
    by admit. (* x \in E, E: {set ordinal_inType 0} => absurd *)
  + (* n ~ n.+1 *)
    case: b H HE=> H HE.
    - (* b ~ true *)
      have ->: fill_ntz [tuple of true :: bs] = [tuple of true :: ones n].
        apply val_inj.
        by rewrite /= size_tuple //.
      rewrite /=.
      rewrite count_true.
      rewrite addnC addn1 subnn.
      admit. (* i is minimum of true :: ... => i = 0 *)
    - (* b ~ false *)
      have Hrec: fill_ntz [tuple of false :: bs] = [tuple of false :: (fill_ntz bs)]
        by apply val_inj.
      rewrite Hrec.
      rewrite Hrec in H.
      rewrite /=.
      rewrite add0n subSn //.
      have eq_n_m: n.-1.+1 = n by admit.
      set x' := cast_ord eq_n_m (inord (n' := n.-1) (x.-1)).
      set E' := [ set x : 'I_n | inord (x.+1) \in E ].
      set ntzE' := [ set x : 'I_n | inord (x.+1) \in ntzE ].
      have repr_bs: repr bs E' by apply (repr_rec n bs E false).
      have x'_in_E': x' \in E' by admit.
      set i' := (cast_ord eq_n_m (inord (n' := n.-1) (i.-1))).
      have i'_in_E': i' \in E' by admit.
      have minH: forall j, j \in E' -> i' <= j by admit.
      rewrite (IHn bs x' E' repr_bs x'_in_E' i' i'_in_E' minH ntzE').
      rewrite /i'.
      admit.
      rewrite /ntzE'.
      apply (repr_rec n (fill_ntz bs) ntzE false)=> //.
      admit. (* count_mem true (..) <= n *)
      admit. (* TODO: only enable the case when 2 ^ k %| n *)
Admitted.
