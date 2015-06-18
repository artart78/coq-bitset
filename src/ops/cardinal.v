From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div finset ssralg zmodp.
From Bits
     Require Import bits tuple.
Require Import props.bineqs props.getbit props.tozp spec.

Definition pop_table (n: nat) := mkseq (fun i => count_mem true (fromNat (n := n) i)) (2^n).

Definition pop_elem {n}(k: nat)(bs: BITS n)(i: nat): nat
  := let x := andB (shrBn bs (i * 2^k)) (decB (shlBn #1 (2^k))) in
     nth 0 (pop_table (2^k)) (toNat x).

Fixpoint popAux {n}(k: nat)(bs: BITS n)(i: nat): nat :=
  match i with
  | 0 => 0
  | i'.+1 => (pop_elem k bs i') + (popAux k bs i')
  end.

Definition cardinal {n}(k: nat)(bs: BITS n): nat
  := popAux k bs (n %/ 2^k).

Lemma count_tcast:
  forall n m (bs: BITS n) (H: n = m), count_mem true (tcast H bs) = count_mem true bs.
Proof.
  move=> n m bs H.
  by case: m / H.
Qed.

Lemma count_low:
  forall n (bs: BITS n) k (H: n = 2 ^ k + (n - 2 ^ k)), toNat (n := n) bs < 2 ^ 2 ^ k ->
      (forall i, i < n -> 2 ^ k <= i -> getBit bs i = false) ->
      count_mem true (fromNat (n := 2 ^ k) (toNat (n := n) bs))
    = count_mem true (low (2 ^ k) (tcast H bs)).
Proof.
  move=> n bs k H le_n high_bits.
  have ->: fromNat (n := 2 ^ k) (toNat (n := n) bs)
         = low (2 ^ k) (fromNat (n := 2 ^ k + (n - 2 ^ k)) (toNat (n := n) bs)).
    rewrite low_fromNat //.
  have ->: fromNat (n := 2 ^ k + (n - 2 ^ k)) (toNat (n := n) bs)
         = tcast H (fromNat (n := n) (toNat (n := n) bs)).
    apply allBitsEq=> i le_i.
    rewrite getBit_tcast.
    by case: (2 ^ k + (n - 2 ^ k)) / H.
  rewrite toNatK //.
Qed.

Lemma pop_elem_repr:
  forall n k i (bs: BITS n)(q: n = i.+1 * 2 ^ k + (n - i.+1 * 2 ^ k))(q': i.+1 * 2 ^ k = i * 2 ^ k + 2 ^ k)(H: i.+1 * 2 ^ k <= n),
    pop_elem k bs i = count_mem true (high (2 ^ k) (tcast q' (low (i.+1 * 2 ^ k) (tcast q bs)))).
Proof.
  move=> n k i bs q q' H1.
  have le_2k: 2 ^ k < n.+1.
    rewrite (leq_ltn_trans (n := i.+1 * 2 ^ k)) //.
    rewrite -[i.+1]addn1.
    rewrite mulnDl.
    rewrite mul1n.
    rewrite -{1}[2 ^ k]add0n.
    by rewrite leq_add2r //.
  have H: n = 2 ^ k + (n - 2 ^ k).
    by rewrite subnKC.
  have H': 2 ^ k + (n - 2 ^ k) = n by rewrite -H.
  rewrite /pop_elem.
  rewrite /pop_table.
  set bs' := andB (shrBn bs (i * 2 ^ k)) (decB (shlBn #1 (2 ^ k))).
  have H'': toNat bs' < 2 ^ 2 ^ k.
    have ltn_ones: toNat (n := n) (decB (shlBn #1 (2 ^ k))) < 2 ^ 2 ^ k.
      rewrite makeOnes2=> //.
      rewrite toNat_tcast toNatCat toNat_zero toNat_ones mul0n add0n.
      rewrite -(ltn_add2r 1).
      rewrite !addn1.
      rewrite prednK //.
      rewrite expn_gt0.
      by auto with arith.
    rewrite (leq_ltn_trans (n := toNat (n := n) (decB (shlBn #1 (2 ^ k))))) //.
    rewrite -leB_nat.
    by rewrite leB_andB.
  rewrite nth_mkseq=> //.

  have ->: high (2 ^ k) (tcast q' (low (i.+1 * 2 ^ k) (tcast q bs)))
  = low (2 ^ k) (tcast H (andB (shrBn bs (i * 2 ^ k)) (decB (shlBn #1 (2 ^ k))))).
  rewrite makeOnes2.
  apply allBitsEq=> i0 le_i0.
  have H''': i0 < n.
    apply (leq_trans (n := i.+1 * 2 ^ k)).
    apply (leq_trans (n := 2 ^ k)).
    apply le_i0.
    have {1}->: 2 ^ k = 1 * 2 ^ k by auto with arith.
    rewrite leq_mul2r.
    have ->: 0 < i.+1 by auto with arith.
    rewrite orbT //.
    rewrite H1 //.
  rewrite getBit_low.
  rewrite le_i0.
  rewrite getBit_high.
  rewrite !getBit_tcast.
  rewrite getBit_low.
  have ->: i0 + i * 2 ^ k < i.+1 * 2 ^ k.
  rewrite -[i.+1]add1n.
  rewrite mulnDl.
  rewrite ltn_add2r.
  rewrite mul1n.
  apply le_i0.
  rewrite getBit_tcast.
  rewrite getBit_liftBinOp.
  rewrite getBit_tcast.
  rewrite getBit_catB.
  rewrite le_i0.
  rewrite getBit_ones.
  rewrite andbT.
  rewrite getBit_shrBn.
  rewrite addnC //.
  rewrite (leq_trans (n := i * 2 ^ k + 2 ^ k)) //.
  rewrite ltn_add2l le_i0 //.
  have {2}->: 2 ^ k = 1 * 2 ^ k by auto with arith.
  rewrite -mulnDl addn1.
  rewrite H1 //.
  rewrite le_i0 //.
  apply H'''.

  apply le_2k.
  apply count_low.
  apply H''.
  move=> i0 lt_i0 ge_i0.
  rewrite getBit_liftBinOp=> //.
  rewrite makeOnes2=> //.
  rewrite getBit_tcast.
  rewrite getBit_catB.
  have ->: (i0 < 2 ^ k) = false.
    by rewrite ltnNge ge_i0.
  rewrite -fromNat0.
  rewrite getBit_zero.
  by rewrite andbF.
Qed.

Lemma pop_rec:
  forall n k i (bs: BITS n)(q: n = i * 2 ^ k + (n - i * 2 ^ k))(H: i * 2 ^ k <= n),
    popAux k bs i = count_mem true (low (i * (2 ^ k)) (tcast q bs)).
Proof.
  move=> n k i.
  move: i n.
  elim=> [|i IHi] n bs q le_i.
  + (* i ~ 0 *)
    by rewrite /=.
  + (* i ~ i.+1 *)
    rewrite /popAux.
    rewrite -/popAux.

    have Hi: i * 2 ^ k < n => //.
      rewrite (leq_trans (n := i.+1 * 2 ^ k)) //.
      rewrite ltn_mul2r.
      rewrite -ltnS.
      have ->: i < i.+1 by auto with arith.
      have H: 2 ^ k > 0.
        rewrite expn_gt0.
        have ->: 0 < 2 by auto with arith.
        rewrite orbC orbT //.
      have ->: 1 < (2 ^ k).+1 by auto with arith.
      rewrite andbT //.

    rewrite IHi=> //.
    rewrite subnKC //.

    rewrite ltnW //.
    move=> H0.
    rewrite pop_elem_repr.
    rewrite -addn1.
    rewrite mulnDl.
    auto with arith.
    move=> H1.
    have H2: i * 2 ^ k + 2 ^ k = i.+1 * 2 ^ k by auto with arith.
    have {2}->: low (i.+1 * 2 ^ k) (tcast q bs)
    = tcast H2 ((high (2 ^ k) (tcast H1 (low (i.+1 * 2 ^ k) (tcast q bs))) ##
      low (i * 2 ^ k) (tcast H0 bs))).
      apply allBitsEq=> i0 le_i0.
      rewrite getBit_low.
      rewrite le_i0.
      rewrite getBit_tcast.
      rewrite getBit_tcast.
      rewrite getBit_catB.
      case H: (i0 < i * 2 ^ k).
      + (* i0 < i * 2 ^ k *)
        by rewrite getBit_low H getBit_tcast.
      + (* i0 >= i * 2 ^ k *)
        rewrite getBit_high getBit_tcast getBit_low getBit_tcast.
        rewrite subnK.
        rewrite le_i0 //.
        rewrite leqNgt.
        by rewrite H //.
    rewrite count_tcast.
    rewrite count_cat addnC //.
    rewrite le_i //.
    rewrite ltnW //.
Qed.

Lemma cardinal_repr:
  forall n k (bs: BITS n) E, 2 ^ k %| n -> repr bs E ->
    cardinal k bs = #|E|.
Proof.
  move=> n k bs E div_2k_n HE.
  have H1: n = n %/ 2 ^ k * 2 ^ k.
    by rewrite divnK //.
  rewrite /cardinal pop_rec.
  rewrite divnK=> //.
  rewrite subnKC //.
  move=> H0.
  have ->: low (n %/ 2 ^ k * 2 ^ k) (tcast H0 bs) = tcast H1 bs.
    apply allBitsEq=> i le_i.
    by rewrite getBit_low le_i !getBit_tcast.
  rewrite count_tcast.
  by apply count_repr.
  by rewrite -H1.
Qed.
