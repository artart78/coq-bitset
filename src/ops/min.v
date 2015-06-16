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

Lemma index_repr:
  forall n (bs: BITS n) x E, repr bs E -> x \in E ->
    index true bs = [arg min_(k < x in E) k].
Proof.
  elim=> [bs|n IHn /tupleP[b bs]] x E HE Hx.
  + (* n ~ 0 *)
    by move: x Hx=> [x le_x].
  + (* n ~ n.+1 *)
    case: b HE=> HE.
    - (* b ~ true *)
      rewrite /=.
      case: arg_minP=> // i Hi Hj.
      have H: i <= 0.
        rewrite (Hj ord0) //.
        rewrite HE in_set //=.
      move/eqP: H=>H.
      rewrite subn0 in H.
      apply esym.
      by rewrite H.
    - (* b ~ false *)
      rewrite /=.
      set E' := [ set x : 'I_n | inord(x.+1) \in E ].
      have HpredK: (n.-1).+1 = n by admit. (* We can't have n = 0, otherwise repr [false] E and x \in E, which is not possible! *)
      set x' := cast_ord HpredK (inord (n' := n.-1) x.-1).
      have Hx': x' \in E'.
        rewrite in_set.
        rewrite /=.
        rewrite inordK.
        have ->: x.-1.+1 = x by admit.
        have ->: inord (n' := n) x = x.
          apply ord_inj.
          rewrite inordK //.
        apply Hx.
        admit. (* x.-1 < n.-1.+1 *)
      have HE': repr bs E' by apply (repr_rec n bs E false).
      case: arg_minP=> // i Hi Hj.
      rewrite (IHn bs x' E')=> //.
      case: arg_minP=> // i' Hi' Hj'.
      have H1: i <= inord (n' := n) i'.+1.
        rewrite (Hj (inord i'.+1)) //.
        rewrite HE.
        rewrite in_set.
        have ->: getBit [tuple of false :: bs] (inord (n' := n) i'.+1) = getBit bs i'.
          rewrite inordK //.
          rewrite -[i'.+1]addn1 -[n.+1]addn1.
          rewrite ltn_add2r.
          rewrite ltn_ord //.
        rewrite HE' in Hi'.
        rewrite in_set in Hi'.
        apply Hi'.
      have H2: i' <= cast_ord HpredK (inord (n' := n.-1) i.-1).
        rewrite (Hj' (cast_ord HpredK (inord (n' := n.-1) i.-1))) //.
        rewrite HE'.
        rewrite in_set.
        have ->: getBit bs (cast_ord HpredK (inord i.-1)) = getBit [tuple of false :: bs] i.
          rewrite /=.
          have {2}->: nat_of_ord i = i.-1.+1.
            by admit.
          have ->: getBit [tuple of false :: bs] i.-1.+1 = getBit bs i.-1 by compute.
          rewrite inordK //.
          admit. (* i.-1 < n.-1.+1 *)
        rewrite HE in Hi.
        rewrite in_set in Hi.
        apply Hi.
      have H': i'.+1 == i.
        rewrite eqn_leq.
        have ->: i <= i'.+1.
          rewrite inordK in H1.
          apply H1.
          rewrite -[i'.+1]addn1 -[n.+1]addn1.
          rewrite ltn_add2r //.
        have ->: i'.+1 <= i.
          rewrite /= in H2.
          rewrite inordK in H2.
          have ->: nat_of_ord i = i.-1.+1.
            by admit. (* See above. *)
          rewrite -[i'.+1]addn1 -[i.-1.+1]addn1.
          rewrite leq_add2r.
          apply H2.
          rewrite !prednK.
          rewrite -(leq_add2r 1).
          rewrite !addn1.
          rewrite ltn_ord //.
          admit. (* 0 < n *)
          admit. (* 0 < i *)
        rewrite //=.
      move/eqP: H' ->.
      rewrite //.
Admitted.

Lemma ntz_repr:
  forall n (bs: BITS n) k x E, repr bs E -> x \in E ->
    ntz k bs = [arg min_(k < x in E) k].
Proof.
  move=> n bs k x E HE Hx.
  rewrite -(index_repr n bs x E)=> //.
  rewrite /ntz fill_ntz_repr.
  set ntzE := [ set x : 'I_n | getBit (fill_ntz bs) x ].
  have H: repr (fill_ntz bs) ntzE=> //.
  rewrite (cardinal_repr n k (fill_ntz bs) ntzE)=> //.
  rewrite -(count_repr n (fill_ntz bs) ntzE)=> //.
  clear x E Hx HE ntzE H.
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
