From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import props.getbit.

Definition repr {n}(bs: BITS n) E :=
  E = [ set x : 'I_n | getBit bs x ].

Lemma repr_rec:
  forall n (bs: BITS n) E b, repr [tuple of b :: bs] E ->
    repr bs [ set x : 'I_n | inord(x.+1) \in E ].
Proof.
  move=> n bs E b.
  rewrite !/repr -!setP !/eq_mem=> HE i.
  rewrite in_set HE !in_set inordK.
  rewrite /getBit -nth_behead //=.
  have ltn_i: i < n by apply ltn_ord.
  by auto with arith.
Qed.

Lemma singleton_repr:
  forall n (k: 'I_n), repr (setBit #0 k true) [set k].
Proof.
  move=> n k.
  rewrite /repr -setP /eq_mem=> x.
  rewrite !in_set.
  case x_eq_k: (x == k).
  + (* x == k *)
    move/eqP: x_eq_k ->.
    by rewrite setBitThenGetSame.
  + (* x <> k *)
    rewrite setBitThenGetDistinct=> //.
    rewrite getBit_zero //.
    apply not_eq_sym.
    move=> x_is_k.
    move/eqP: x_eq_k=>x_eq_k.
    apply x_eq_k.
    by apply ord_inj.
Qed.

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
      have gtz_E: forall z, z \in E -> z > 0.
        move=> [z le_z] Hz.
        case: z le_z Hz=> // le_z Hz.
        rewrite HE in Hz.
        rewrite in_set in Hz.
        rewrite /= in Hz.
        by rewrite //.
      have gtz_n: n > 0.
        clear IHn HE E'.
        case: n bs x E Hx gtz_E=> [bs|] // x E Hx gtz_E.
        move: x Hx=> [x le_x] Hx.
        have H': x = 0.
          by elim: x le_x Hx=> // le_x Hx.
        rewrite -{2}H'.
        rewrite (gtz_E (Ordinal le_x)) //.
      have HpredK: n.-1.+1 = n.
        by rewrite prednK.
      set x' := cast_ord HpredK (inord (n' := n.-1) x.-1).
      have Hx': x' \in E'.
        rewrite in_set.
        rewrite /=.
        rewrite inordK.
        have ->: x.-1.+1 = x.
          rewrite prednK //.
          by rewrite (gtz_E x) //.
        have ->: inord (n' := n) x = x.
          apply ord_inj.
          rewrite inordK //.
        apply Hx.
        rewrite !prednK.
        rewrite -(leq_add2r 1).
        rewrite !addn1.
        rewrite ltn_ord //.
        rewrite //.
        by rewrite (gtz_E x) //.
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
            rewrite prednK //.
            by rewrite (gtz_E i).
          have ->: getBit [tuple of false :: bs] i.-1.+1 = getBit bs i.-1 by compute.
          rewrite inordK //.
          rewrite !prednK.
          rewrite -(leq_add2r 1).
          rewrite !addn1.
          rewrite ltn_ord //.
          rewrite //.
          by rewrite (gtz_E i).
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
            rewrite prednK //.
            by rewrite (gtz_E i).
          rewrite -[i'.+1]addn1 -[i.-1.+1]addn1.
          rewrite leq_add2r.
          apply H2.
          rewrite !prednK.
          rewrite -(leq_add2r 1).
          rewrite !addn1.
          rewrite ltn_ord //.
          rewrite //.
          by rewrite (gtz_E i).
        rewrite //=.
      move/eqP: H' ->.
      rewrite //.
Qed.

Lemma count_repr:
  forall n (bs: BITS n) E, repr bs E ->
    count_mem true bs = #|E|.
Proof.
  elim=> [bs|n IHn /tupleP[b bs]] E HE.
  + (* n ~ 0 *)
    rewrite tuple0 /=.
    rewrite eq_card0 //.
    rewrite /eq_mem=> x.
    by move: x => [x le_x].
  + (* n ~ n.+1 *)
    rewrite /=.
    rewrite HE.
    rewrite (cardD1 ord0).
    have ->: #|[predD1 [set x : 'I_n.+1 | getBit [tuple of b :: bs] x] & ord0]|
           = #|[set x : 'I_n | getBit bs x]|.
      have H: injective (fun (x : 'I_n) => inord (n' := n) x.+1).
        rewrite /injective=> x1 x2 H.
        have H': x1.+1 = x2.+1.
          (* TODO: factorize *)
          have ->: x1.+1 = nat_of_ord (inord (n' := n) x1.+1).
            rewrite inordK //.
            rewrite -[x1.+1]addn1 -[n.+1]addn1.
            rewrite ltn_add2r.
            by rewrite ltn_ord.
          have ->: x2.+1 = nat_of_ord (inord (n' := n) x2.+1).
            rewrite inordK //.
            rewrite -[x2.+1]addn1 -[n.+1]addn1.
            rewrite ltn_add2r.
            by rewrite ltn_ord.
          rewrite H //.
        apply ord_inj.
        have H1': x1.+1 == x2.+1.
          apply/eqP.
          apply H'.
        apply/eqP.
        by rewrite -eqSS.
      rewrite -(card_image H).
      apply eq_card.
      rewrite /eq_mem=> x.
      rewrite !unfold_in.
      rewrite /=.
      rewrite in_set.
      case eq0: (x == ord0).
      + (* x == ord0 *)
        rewrite /=.
        apply/eqP/imageP.
        move=> absH.
        have [x1 H1 H2] := absH.
        have H': x = ord0.
          move/eqP: eq0=> //.
        rewrite H' in H2.
        have: 0 = x1.+1.
        have ->: 0 = nat_of_ord (ord0 (n' := n)) by rewrite //.
        have ->: x1.+1 = nat_of_ord (inord (n' := n) x1.+1).
          rewrite inordK //.
          rewrite -[x1.+1]addn1 -[n.+1]addn1.
          rewrite ltn_add2r.
          by rewrite ltn_ord.
        rewrite H2 //.
        by rewrite //.
      + (* x <> ord0 *)
        rewrite /=.
        apply/eqP.
        have gtz_x: x > 0.
          move: x eq0=> [x le_x] eq0.
          by elim: x le_x eq0=> // le_x eq0.
        have H'': nat_of_ord x = x.-1.+1.
          by rewrite prednK //.
        have le_x: x.-1 < n.
          rewrite -(ltn_add2r 1).
          rewrite !addn1.
          rewrite -H''.
          by rewrite ltn_ord.
        case H': (getBit [tuple of b :: bs] x).
        - (* getBit [tuple of b :: bs] x == true *)
          apply/imageP.
          exists (Ordinal le_x).
          rewrite in_set /=.
          rewrite H'' in H'.
          have ->: getBit bs x.-1 = getBit [tuple of b :: bs] x.-1.+1 by compute.
          rewrite H' //.
          rewrite /=.
          rewrite -H''.
          have: nat_of_ord x = nat_of_ord (inord (n' := n) x).
            by rewrite inordK //.
          apply ord_inj.
        - (* getBit [tuple of b :: bs] x == false *)
          apply/imageP.
          elim=> x' Hx' Hxx'.
          rewrite Hxx' in H'.
          have H1: getBit [tuple of b :: bs] (inord (n' := n) x'.+1) = getBit bs x'.
            rewrite inordK.
            by compute.
          rewrite -[x'.+1]addn1 -[n.+1]addn1.
          rewrite ltn_add2r.
          rewrite ltn_ord //.
          rewrite in_set in Hx'.
          rewrite Hx' in H1.
          rewrite H1 in H'.
          by rewrite //.
    rewrite in_set /=.
    have ->: getBit [tuple of b :: bs] 0 = b by compute.
    set E' := [set x : 'I_n | getBit bs x].
    rewrite (IHn bs E')=> //.
    case: b HE=> //.
Qed.
