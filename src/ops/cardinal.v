From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div finset ssralg zmodp.
From Bits
     Require Import bits ssrextra.tuple.
Require Import props.bineqs props.getbit props.tozp spec.

(** * Cardinal through binary population count  *)

(* TODO: add ref. to Hacker's delight *)
(* TODO: document the algorithm *)

Definition pop_table (n: nat) := mkseq (fun i => count_mem true (fromNat (n := n) i)) (2^n).

Definition pop_elem {n}(k: nat)(bs: BITS n)(i: nat): nat
  := let x := andB (shrBn bs (i * k)) (decB (shlBn #1 k)) in
     nth 0 (pop_table k) (toNat x).

Fixpoint popAux {n}(k: nat)(bs: BITS n)(i: nat): nat :=
  match i with
  | 0 => 0
  | i'.+1 => (pop_elem k bs i') + (popAux k bs i')
  end.

Definition cardinal {n}(k: nat)(bs: BITS n): nat
  := popAux k bs (n %/ k).

Lemma count_tcast:
  forall n m (bs: BITS n) (H: n = m), count_mem true (tcast H bs) = count_mem true bs.
Proof.
  move=> n m bs H.
  by case: m / H.
Qed.

(* TODO: passing the associative/commutative proofs by hand is an
         annoyance. That's something to ponder.. *)

Lemma pop_elem_repr:
  forall n k i (bs: BITS n)
         (q: n = i.+1 * k + (n - i.+1 * k))
         (q': i.+1 * k = i * k + k),
    i.+1 * k <= n ->
        pop_elem k bs i = count_mem true (high k (tcast q' (low (i.+1 * k) (tcast q bs)))).
Proof.
  move=> n k i bs q q' leq_Sik.
  have le_k: k < n.+1.
    rewrite (leq_ltn_trans (n := i.+1 * k)) //.
    by rewrite -[i.+1]addn1 mulnDl mul1n -{1}[k]add0n leq_add2r.
  have H: n = k + (n - k).
    by rewrite subnKC.
  have H': k + (n - k) = n by rewrite -H.
  rewrite /pop_elem /pop_table.
  rewrite makeOnes2=> //.
  set bs' := andB (shrBn bs (i * k)) (tcast H' (zero (n - k) ## ones k)).
  have toNat_bounded: toNat bs' < 2 ^ k.
    have ltn_ones: toNat (n := n) (tcast H' (zero (n - k) ## ones k)) < 2 ^ k.
      rewrite toNat_tcast toNatCat toNat_zero toNat_ones mul0n add0n
              -(ltn_add2r 1) !addn1 prednK // expn_gt0.
      by auto with arith.
    by rewrite (leq_ltn_trans (n := toNat (n := n) (tcast H' (zero (n - k) ## ones k)))) //
              -leB_nat leB_andB.
  rewrite nth_mkseq=> //.

  have ->: high k (tcast q' (low (i.+1 * k) (tcast q bs)))
         = low k (tcast H (andB (shrBn bs (i * k)) (tcast H' (zero (n - k) ## ones k)))).
    apply allBitsEq=> i0 ltn_i0_k.
    have ltn_i0_n: i0 < n.
      apply (leq_trans (n := i.+1 * k))=> //.
      apply (leq_trans (n := k))=> //.
      have {1}->: k = 1 * k by auto with arith.
      by rewrite leq_mul2r orbT.
    rewrite getBit_low ltn_i0_k getBit_high !getBit_tcast getBit_low.
    have ->: i0 + i * k < i.+1 * k.
      by rewrite -[i.+1]add1n mulnDl ltn_add2r mul1n.
    rewrite getBit_tcast getBit_liftBinOp=> //.
    rewrite getBit_tcast getBit_catB ltn_i0_k getBit_ones=> //.
    rewrite andbT getBit_shrBn addnC //.
    rewrite addnC (leq_trans (n := i * k + k)) //.
    rewrite ltn_add2l ltn_i0_k //.
    have {2}->: k = 1 * k by auto with arith.
    by rewrite -mulnDl addn1.

  have ->: fromNat (n := k) (toNat (n := n) bs')
         = low k (fromNat (n := k + (n - k)) (toNat (n := n) bs')).
    by rewrite low_fromNat.
  have ->: fromNat (n := k + (n - k)) (toNat (n := n) bs')
         = tcast H (fromNat (n := n) (toNat (n := n) bs')).
    apply allBitsEq=> i0 le_i0.
    rewrite getBit_tcast.
    by case: (k + (n - k)) / H.
  by rewrite toNatK.
Qed.

Lemma pop_rec:
  forall n k i (bs: BITS n)
         (q: n = i * k + (n - i * k)),
    i * k <= n -> k > 0 ->
        popAux k bs i = count_mem true (low (i * k) (tcast q bs)).
Proof.
  move=> n k i.
  move: i n.
  elim=> [|i IHi] n bs q le_i k_gtz.
  + (* i ~ 0 *)
    by rewrite /=.
  + (* i ~ i.+1 *)
    rewrite /popAux -/popAux.
    have ltn_i2k: i * k < n.
      rewrite (leq_trans (n := i.+1 * k)) // ltn_mul2r -ltnS.
      have ->: i < i.+1 by auto with arith.
      have ->: 1 < k.+1 by auto with arith.
      by rewrite /=.
    have leq_i2k: i * k <= n.
      by rewrite ltnW.

    rewrite IHi=> //.
    rewrite subnKC //.

    move=> Hcast0.
    rewrite pop_elem_repr=> //.
    rewrite -addn1 mulnDl.
    auto with arith.
    move=> Hcast1.
    have Hcast2: i * k + k = i.+1 * k by auto with arith.
    have {2}->: low (i.+1 * k) (tcast q bs)
    = tcast Hcast2 ((high k (tcast Hcast1 (low (i.+1 * k) (tcast q bs))) ##
      low (i * k) (tcast Hcast0 bs))).
      apply allBitsEq=> i0 le_i0.
      rewrite getBit_low le_i0 !getBit_tcast getBit_catB.
      case H: (i0 < i * k).
      + (* i0 < i * k *)
        by rewrite getBit_low H getBit_tcast.
      + (* i0 >= i * k *)
        rewrite getBit_high getBit_tcast getBit_low getBit_tcast subnK.
        rewrite le_i0 //.
        by rewrite leqNgt H //.
    by rewrite count_tcast count_cat addnC.
Qed.

Lemma cardinal_repr:
  forall n k (bs: BITS n) E,
    k %| n -> k > 0 -> repr bs E ->
        cardinal k bs = #|E|.
Proof.
  move=> n k bs E div_k_n gtz_k HE.
  have Hcast1: n = n %/ k * k.
    by rewrite divnK=> //.
  rewrite /cardinal pop_rec=> //.
  rewrite -Hcast1.
  rewrite subnKC //.
  move=> Hcast0.
  have ->: low (n %/ k * k) (tcast Hcast0 bs) = tcast Hcast1 bs.
    apply allBitsEq=> i le_i.
    by rewrite getBit_low le_i !getBit_tcast.
  rewrite count_tcast.
  apply count_repr=> //.
  by rewrite -Hcast1.
Qed.
