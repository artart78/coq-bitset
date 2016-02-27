Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.

Definition repr {n}(bs: BITS n) E := E = [ set x : 'I_n | getBit bs x ].

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

Lemma eq_repr:
  forall n (bs: BITS n) (bs': BITS n) E E', repr bs E -> repr bs' E' ->
    (bs == bs') = (E == E').
Proof.
  move=> n bs bs' E E' H H'.
  rewrite /repr in H.
  rewrite /repr in H'.
  case Heq: (E == E').
  + (* E == E' *)
    apply/eqP.
    apply allBitsEq=> i ltn_i.
    move/eqP: Heq=> Heq.
    move/setP: Heq=> Heq.
    move: (Heq (Ordinal ltn_i))=> Heqi.
    rewrite H H' !in_set in Heqi.
    by apply Heqi.
  + (* E <> E' *)
    case Hbs: (bs == bs')=> //.
    move/eqP: Hbs=> Hbs.
    have Habs: E == E'.
      apply/eqP.
      rewrite -setP /eq_mem=> i.
      rewrite H H' !in_set.
      by rewrite Hbs.
    by rewrite Habs in Heq.
Qed.

Lemma empty_repr:
  forall n, repr (zero n) set0.
Proof.
  move=> n.
  rewrite /repr -setP /eq_mem=> i.
  by rewrite in_set in_set0 -fromNat0 getBit_zero.
Qed.

Lemma subset_repr:
  forall k n, k <= n -> repr (decB (shlBn #1 k)) [set x : 'I_n | x < k].
Proof.
  move=> k n le_k.
  rewrite makeOnes=> //.
  rewrite subnKC //.
  move=> ?.
  rewrite /repr -setP /eq_mem=> i.
  rewrite !in_set.
  rewrite getBit_tcast.
  rewrite getBit_catB.
  case ltn_i: (i < k).
  + (* i < k *)
    by rewrite getBit_ones.
  + (* i >= k *)
    by rewrite -fromNat0 getBit_zero.
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
    case: b HE=> /= HE.
    - (* b ~ true *)
      case: arg_minP=> // i Hi Hj.
      have H: i <= 0.
        rewrite (Hj ord0) //.
        by rewrite HE in_set.
      move/eqP: H=>H.
      rewrite subn0 in H.
      apply esym.
      by rewrite H.
    - (* b ~ false *)
      set E' := [ set x : 'I_n | inord(x.+1) \in E ].
      have gtz_E: forall z, z \in E -> z > 0.
        move=> [z le_z] Hz.
        case: z le_z Hz=> // le_z Hz.
        by rewrite HE in_set /= in Hz.
      have gtz_n: n > 0.
        clear IHn HE E'.
        case: n bs x E Hx gtz_E=> [bs|] // x E Hx gtz_E.
        move: x Hx=> [x le_x] Hx.
        have H': x = 0.
          by elim: x le_x Hx=> // le_x Hx.
        rewrite -{2}H'.
        by rewrite (gtz_E (Ordinal le_x)) //.
      have HpredK: n.-1.+1 = n.
        by rewrite prednK.
      set x' := cast_ord HpredK (inord (n' := n.-1) x.-1).
      have Hx': x' \in E'.
        rewrite in_set /= inordK.
        have ->: x.-1.+1 = x.
          by rewrite prednK // (gtz_E x).
        have ->: inord (n' := n) x = x.
          apply ord_inj.
          by rewrite inordK //.
        apply Hx.
        rewrite !prednK=> //.
        rewrite -(leq_add2r 1) !addn1 ltn_ord //.
        by rewrite (gtz_E x).
      have HE': repr bs E' by apply (repr_rec n bs E false).
      case: arg_minP=> // i Hi Hj.
      rewrite (IHn bs x' E')=> //.
      case: arg_minP=> // i' Hi' Hj'.
      have H1: i <= inord (n' := n) i'.+1.
        rewrite (Hj (inord i'.+1)) // HE in_set.
        have ->: getBit [tuple of false :: bs] (inord (n' := n) i'.+1) = getBit bs i'.
          by rewrite inordK // -[i'.+1]addn1 -[n.+1]addn1 ltn_add2r ltn_ord.
        rewrite HE' in_set in Hi'.
        by apply Hi'.
      have nat_i_prednK: nat_of_ord i = i.-1.+1.
        by rewrite prednK // (gtz_E i).
      have H2: i' <= cast_ord HpredK (inord (n' := n.-1) i.-1).
        rewrite (Hj' (cast_ord HpredK (inord (n' := n.-1) i.-1))) // HE' in_set.
        have ->: getBit bs (cast_ord HpredK (inord i.-1)) = getBit [tuple of false :: bs] i.
          rewrite /= {2}nat_i_prednK.
          have ->: getBit [tuple of false :: bs] i.-1.+1 = getBit bs i.-1 by compute.
          rewrite inordK //.
          rewrite !prednK=> //.
          rewrite -(leq_add2r 1) !addn1 ltn_ord //.
          by rewrite (gtz_E i).
        rewrite HE in_set in Hi.
        by apply Hi.
      have Heq: i'.+1 == i.
        rewrite eqn_leq.
        have ->: i <= i'.+1.
          rewrite inordK in H1.
          apply H1.
          by rewrite -[i'.+1]addn1 -[n.+1]addn1 ltn_add2r.
        have ->: i'.+1 <= i => //.
          rewrite /= inordK in H2.
          rewrite nat_i_prednK -[i'.+1]addn1 -[i.-1.+1]addn1 leq_add2r=> //.
          rewrite !prednK=> //.
          rewrite -(leq_add2r 1) !addn1 ltn_ord //.
          by rewrite (gtz_E i).
      by move/eqP: Heq ->.
Qed.

Lemma count_repr:
  forall n (bs: BITS n) E, repr bs E ->
    count_mem true bs = #|E|.
Proof.
  elim=> [bs|n IHn /tupleP[b bs]] E HE.
  + (* n ~ 0 *)
    rewrite tuple0 /= eq_card0 //.
    rewrite /eq_mem=> x.
    by move: x => [x le_x].
  + (* n ~ n.+1 *)
    rewrite HE (cardD1 ord0).
    have ->: #|[predD1 [set x : 'I_n.+1 | getBit [tuple of b :: bs] x] & ord0]|
           = #|[set x : 'I_n | getBit bs x]|.
      have Hinj: injective (fun (x : 'I_n) => inord (n' := n) x.+1).
        rewrite /injective=> x1 x2 H.
        have Hinj2: x1.+1 = x2.+1.
          (* TODO: factorize *)
          have ->: x1.+1 = nat_of_ord (inord (n' := n) x1.+1).
            by rewrite inordK // -[x1.+1]addn1 -[n.+1]addn1 ltn_add2r ltn_ord.
          have ->: x2.+1 = nat_of_ord (inord (n' := n) x2.+1).
            by rewrite inordK // -[x2.+1]addn1 -[n.+1]addn1 ltn_add2r ltn_ord.
          by rewrite H.
        apply ord_inj.
        have Hinj2': x1.+1 == x2.+1.
          apply/eqP.
          apply Hinj2.
        apply/eqP.
        by rewrite -eqSS.
      rewrite -(card_image Hinj).
      apply eq_card.
      rewrite /eq_mem=> x.
      rewrite !unfold_in /= in_set.
      case eq0: (x == ord0)=> /=.
      + (* x == ord0 *)
        apply/eqP/imageP.
        move=> absH.
        have [x1 H1 H2] := absH.
        have x_eq0: x = ord0.
          by move/eqP: eq0=> //.
        rewrite x_eq0 in H2.
        have: 0 = x1.+1 => //.
        have ->: 0 = nat_of_ord (ord0 (n' := n)) by rewrite //.
        have ->: x1.+1 = nat_of_ord (inord (n' := n) x1.+1).
          by rewrite inordK // -[x1.+1]addn1 -[n.+1]addn1 ltn_add2r ltn_ord.
        by rewrite H2.
      + (* x <> ord0 *)
        apply/eqP.
        have gtz_x: x > 0.
          move: x eq0=> [x le_x] eq0.
          by elim: x le_x eq0=> // le_x eq0.
        have H'': nat_of_ord x = x.-1.+1.
          by rewrite prednK //.
        have le_x: x.-1 < n.
          by rewrite -(ltn_add2r 1) !addn1 -H'' ltn_ord.
        case Hbit: (getBit [tuple of b :: bs] x).
        - (* getBit [tuple of b :: bs] x == true *)
          apply/imageP.
          exists (Ordinal le_x).
          rewrite in_set /=.
          rewrite H'' in Hbit.
          have ->: getBit bs x.-1 = getBit [tuple of b :: bs] x.-1.+1 by compute.
          rewrite Hbit //.
          rewrite /= -H''.
          have: nat_of_ord x = nat_of_ord (inord (n' := n) x).
            by rewrite inordK //.
          apply ord_inj.
        - (* getBit [tuple of b :: bs] x == false *)
          apply/imageP.
          elim=> x' Hx' Hxx'.
          rewrite Hxx' in Hbit.
          have H1: getBit [tuple of b :: bs] (inord (n' := n) x'.+1) = getBit bs x'.
            rewrite inordK.
            by compute.
          rewrite -[x'.+1]addn1 -[n.+1]addn1 ltn_add2r ltn_ord //.
          rewrite in_set in Hx'.
          rewrite Hx' in H1.
          by rewrite H1 in Hbit.
    rewrite in_set /=.
    have ->: getBit [tuple of b :: bs] 0 = b by compute.
    set E' := [set x : 'I_n | getBit bs x].
    rewrite (IHn bs E')=> //.
    by case: b HE.
Qed.
