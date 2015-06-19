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

Lemma pop_elem_repr:
  forall n k i (bs: BITS n)(q: n = i.+1 * 2 ^ k + (n - i.+1 * 2 ^ k))(q': i.+1 * 2 ^ k = i * 2 ^ k + 2 ^ k)(leq_Si2k: i.+1 * 2 ^ k <= n),
    pop_elem k bs i = count_mem true (high (2 ^ k) (tcast q' (low (i.+1 * 2 ^ k) (tcast q bs)))).
Proof.
  move=> n k i bs q q' leq_Si2k.
  have le_2k: 2 ^ k < n.+1.
    rewrite (leq_ltn_trans (n := i.+1 * 2 ^ k)) //.
    by rewrite -[i.+1]addn1 mulnDl mul1n -{1}[2 ^ k]add0n leq_add2r.
  have H: n = 2 ^ k + (n - 2 ^ k).
    by rewrite subnKC.
  have H': 2 ^ k + (n - 2 ^ k) = n by rewrite -H.
  rewrite /pop_elem /pop_table.
  rewrite makeOnes2=> //.
  set bs' := andB (shrBn bs (i * 2 ^ k)) (tcast H' (zero (n - 2 ^ k) ## ones (2 ^ k))).
  have toNat_bounded: toNat bs' < 2 ^ 2 ^ k.
    have ltn_ones: toNat (n := n) (tcast H' (zero (n - 2 ^ k) ## ones (2 ^ k))) < 2 ^ 2 ^ k.
      rewrite toNat_tcast toNatCat toNat_zero toNat_ones mul0n add0n
              -(ltn_add2r 1) !addn1 prednK // expn_gt0.
      by auto with arith.
    by rewrite (leq_ltn_trans (n := toNat (n := n) (tcast H' (zero (n - 2 ^ k) ## ones (2 ^ k))))) //
              -leB_nat leB_andB.
  rewrite nth_mkseq=> //.

  have ->: high (2 ^ k) (tcast q' (low (i.+1 * 2 ^ k) (tcast q bs)))
         = low (2 ^ k) (tcast H (andB (shrBn bs (i * 2 ^ k)) (tcast H' (zero (n - 2 ^ k) ## ones (2 ^ k))))).
    apply allBitsEq=> i0 ltn_i0_2k.
    have ltn_i0_n: i0 < n.
      apply (leq_trans (n := i.+1 * 2 ^ k))=> //.
      apply (leq_trans (n := 2 ^ k))=> //.
      have {1}->: 2 ^ k = 1 * 2 ^ k by auto with arith.
      by rewrite leq_mul2r orbT // leq_Si2k.
    rewrite getBit_low ltn_i0_2k getBit_high !getBit_tcast getBit_low.
    have ->: i0 + i * 2 ^ k < i.+1 * 2 ^ k.
      by rewrite -[i.+1]add1n mulnDl ltn_add2r mul1n.
    rewrite getBit_tcast getBit_liftBinOp=> //.
    rewrite getBit_tcast getBit_catB ltn_i0_2k getBit_ones=> //.
    rewrite andbT getBit_shrBn addnC //.
    rewrite addnC (leq_trans (n := i * 2 ^ k + 2 ^ k)) //.
    rewrite ltn_add2l ltn_i0_2k //.
    have {2}->: 2 ^ k = 1 * 2 ^ k by auto with arith.
    by rewrite -mulnDl addn1 leq_Si2k //.

  have ->: fromNat (n := 2 ^ k) (toNat (n := n) bs')
         = low (2 ^ k) (fromNat (n := 2 ^ k + (n - 2 ^ k)) (toNat (n := n) bs')).
    by rewrite low_fromNat.
  have ->: fromNat (n := 2 ^ k + (n - 2 ^ k)) (toNat (n := n) bs')
         = tcast H (fromNat (n := n) (toNat (n := n) bs')).
    apply allBitsEq=> i0 le_i0.
    rewrite getBit_tcast.
    by case: (2 ^ k + (n - 2 ^ k)) / H.
  by rewrite toNatK.
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
    rewrite /popAux -/popAux.
    have ltn_i2k: i * 2 ^ k < n.
      rewrite (leq_trans (n := i.+1 * 2 ^ k)) // ltn_mul2r -ltnS.
      have ->: i < i.+1 by auto with arith.
      have H: 2 ^ k > 0.
        rewrite expn_gt0.
        by auto with arith.
      have ->: 1 < (2 ^ k).+1 by auto with arith.
      by rewrite /=.
    have leq_i2k: i * 2 ^ k <= n.
      by rewrite ltnW.

    rewrite IHi=> //.
    rewrite subnKC //.

    move=> Hcast0.
    rewrite pop_elem_repr=> //.
    rewrite -addn1 mulnDl.
    auto with arith.
    move=> Hcast1.
    have Hcast2: i * 2 ^ k + 2 ^ k = i.+1 * 2 ^ k by auto with arith.
    have {2}->: low (i.+1 * 2 ^ k) (tcast q bs)
    = tcast Hcast2 ((high (2 ^ k) (tcast Hcast1 (low (i.+1 * 2 ^ k) (tcast q bs))) ##
      low (i * 2 ^ k) (tcast Hcast0 bs))).
      apply allBitsEq=> i0 le_i0.
      rewrite getBit_low le_i0 !getBit_tcast getBit_catB.
      case H: (i0 < i * 2 ^ k).
      + (* i0 < i * 2 ^ k *)
        by rewrite getBit_low H getBit_tcast.
      + (* i0 >= i * 2 ^ k *)
        rewrite getBit_high getBit_tcast getBit_low getBit_tcast subnK.
        rewrite le_i0 //.
        by rewrite leqNgt H //.
    by rewrite count_tcast count_cat addnC.
Qed.

Lemma cardinal_repr:
  forall n k (bs: BITS n) E, 2 ^ k %| n -> repr bs E ->
    cardinal k bs = #|E|.
Proof.
  move=> n k bs E div_2k_n HE.
  rewrite /cardinal pop_rec divnK=> //.
  rewrite subnKC //.
  move=> Hcast0.
  have ->: low n (tcast Hcast0 bs) = bs.
    apply allBitsEq=> i le_i.
    by rewrite getBit_low le_i getBit_tcast.
  by apply count_repr.
Qed.
