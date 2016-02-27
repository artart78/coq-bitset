Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple div finset.
From Bits
     Require Import bits.
Require Import cardinal spec.

(** * Smallest inhabitant of a set *)

(* TODO: explain the algorithm *)
(* TODO: add ref to Hacker's delight *)


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
        by rewrite /= size_tuple.
      by rewrite /negB /incB /invB /orB /=
                 liftUnOpCons tuple.beheadCons liftBinOpCons orbT
                 -/orB -/invB orB_invB.
    + (* Case: b ~ false *)
      have ->: fill_ntz [tuple of false :: bs] = [tuple of false :: (fill_ntz bs)]
        by apply val_inj.
      by rewrite /negB /incB /invB /orB /=
                 liftUnOpCons tuple.beheadCons liftBinOpCons orbF
                 -/orB IHn.
Qed.

Definition ntz {n}(k: nat)(bs: BITS n): BITS n := subB #n (cardinal k (orB bs (negB bs))).

Lemma ntz_repr:
  forall n (bs: BITS n) k x E, k %| n -> k > 0 -> repr bs E -> x \in E ->
    ntz k bs = #[arg min_(k < x in E) k].
Proof.
  move=> n bs k x E Hk gtz_k HE Hx.
  rewrite -(index_repr n bs x E)=> //.
  rewrite /ntz fill_ntz_repr.
  set ntzE := [ set x : 'I_n | getBit (fill_ntz bs) x ].
  have H: repr (fill_ntz bs) ntzE=> //.
  rewrite (cardinal_repr n k (fill_ntz bs) ntzE)=> //.
  rewrite -(count_repr n (fill_ntz bs) ntzE)=> //.
  clear x E Hx HE ntzE H.
  have H: forall n (bs: BITS n), count_mem true (fill_ntz bs) <= n.
    move=> n0 bs0.
    have {3}->: n0 = size (fill_ntz bs0) by rewrite size_tuple.
    by apply count_size.
  rewrite subB_equiv_addB_negB negB_fromNat.
  rewrite fromNat_addBn addnBA.
  rewrite addnC -addnBA.
  rewrite addnC -fromNat_wrap.
  have ->: n - (count_mem true) (fill_ntz bs) = index true bs.
  move: k Hk gtz_k.
  elim: n bs=> [bs|n IHn /tupleP[b bs]] k Hk gtz_k.
  + (* n ~ 0 *)
    by rewrite tuple0 [bs]tuple0.
  + (* n ~ n.+1 *)
    case: b.
    - (* b ~ true *)
      have ->: fill_ntz [tuple of true :: bs] = [tuple of true :: ones n].
        apply val_inj.
        by rewrite /= size_tuple //.
      by rewrite /= count_ones addnC addn1 subnn.
    - (* b ~ false *)
      have ->: fill_ntz [tuple of false :: bs] = [tuple of false :: (fill_ntz bs)]
        by apply val_inj.
      rewrite /= -(IHn bs 1)=> //.
      rewrite add0n subSn //.
      by apply H.
  rewrite //.
  apply H.
  apply (leq_trans (n := n))=> //.
  rewrite ltnW //.
  apply ltn_expl=> //.
  apply (leq_ltn_trans (n := n))=> //.
  by apply ltn_expl.
Qed.
