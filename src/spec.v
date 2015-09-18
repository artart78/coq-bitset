From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.
Require Import props.bineqs props.getbit.

Definition repr {T: finType}{n}(bs: BITS n)(E: {set T}) :=
  forall k : 'I_#|T|, enum_val k \in E <-> getBit bs k.

Lemma repr_rec:
  forall n (bs: BITS n) (T: finType) (E: {set T}) b (H: n.+1 = #|T|), repr [tuple of b :: bs] E ->
    repr bs [ set (enum_val x) | x in [ set x : 'I_#|T| | enum_val (cast_ord H (inord x.+1)) \in E ] ].
Proof.
  move=> n bs T E b H.
  rewrite !/repr=> HE i.
  apply (iff_trans (B := getBit [tuple of b :: bs] (cast_ord H (inord i.+1)))).
  apply (iff_trans (B := enum_val (cast_ord H (inord i.+1)) \in E)).
  have ->: enum_val i
     \in [set enum_val x
            | x in [set x : 'I_#|T| | enum_val (cast_ord H (inord x.+1)) \in E]] = ((enum_val (cast_ord H (inord i.+1))) \in E)
    by admit.
  rewrite //.
  apply (HE (cast_ord H (inord i.+1))).
  have ->: nat_of_ord (cast_ord H (inord i.+1)) = i.+1 by admit.
  by rewrite /getBit -nth_behead.
Admitted.

Lemma eq_repr {T: finType}:
  forall n (bs: BITS n) (bs': BITS n) (E: {set T}) E' (q: n = #|T|), repr bs E -> repr bs' E' ->
    (bs == bs') = (E == E').
Proof.
  move=> n bs bs' E E' q H H'.
  rewrite /repr in H.
  rewrite /repr in H'.
  case Heq: (E == E').
  + (* E == E' *)
    apply/eqP.
    apply allBitsEq=> i ltn_i.
    move/eqP: Heq=> Heq.
    move/setP: Heq=> Heq.
    move: (Heq (enum_val (cast_ord q (Ordinal ltn_i))))=> Heqi.
    admit.
  + (* E <> E' *)
    case Hbs: (bs == bs')=> //.
    move/eqP: Hbs=> Hbs.
    have Habs: E == E'.
      apply/eqP.
      rewrite -setP /eq_mem=> i.
      admit.
    by rewrite Habs in Heq.
Admitted.

Lemma empty_repr:
  forall n T, repr (T := T) (zero n) set0.
Proof.
  move=> n T.
  rewrite /repr=> k.
  by rewrite in_set0 -fromNat0 getBit_zero.
Qed.

Lemma subset_repr:
  forall k n, k <= n -> repr (decB (shlBn (n := n) #1 k)) [set x : 'I_n | x < k].
Proof.
  move=> k n le_k.
  rewrite makeOnes2=> //.
  rewrite subnKC //.
  move=> ?.
  rewrite /repr=> i.
  rewrite !in_set getBit_tcast getBit_catB.
  case ltn_i: (i < k).
  + (* i < k *)
    rewrite enum_val_ord.
    by rewrite getBit_ones.
  + (* i >= k *)
    rewrite enum_val_ord.
    by rewrite -fromNat0 getBit_zero ltn_i.
Qed.

Lemma singleton_repr {T: finType}:
  forall n (k: 'I_n) (q: n = #|T|), repr (n := n) (setBit #0 k true) [set (enum_val (cast_ord q k))].
Proof.
  move=> n k q.
  rewrite /repr=> x.
  rewrite !in_set.
  case x_eq_k: (enum_val x == enum_val (cast_ord q k)).
  + (* x == k *)
    have ->: x = cast_ord q k.
      apply enum_val_inj.
      by apply/eqP.
    by rewrite setBitThenGetSame.
  + (* x <> k *)
    rewrite setBitThenGetDistinct=> //.
    rewrite getBit_zero //.
    by rewrite q.
    apply not_eq_sym.
    move=> x_is_k.
    have Habs: x = cast_ord q k.
      by apply ord_inj.
    by rewrite Habs eq_refl in x_eq_k.
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
