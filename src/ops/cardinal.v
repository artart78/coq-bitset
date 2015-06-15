From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div finset ssralg.
From Bits
     Require Import bits.
Require Import props.getbit props.tozp spec.

(** Recursive algorithm **)

(*

(* Turns off the leftmost bit in a bitvector. *)
Fixpoint off_r_seq (xs: seq bool): seq bool :=
  match xs with
    | [::] => [::]
    | cons false xs => cons false (off_r_seq xs)
    | cons true xs => cons false xs
  end.

Lemma off_rP {n}(t: BITS n): size (off_r_seq t) == n.
Proof.
  elim: n t=> [t|n IH /tupleP [b t]] //=.
  - (* Case: n ~ 0 *)
    by rewrite (tuple0 t).
  - (* Case: n ~ n.+1 *)
    case: b=> //=.
    + (* Case: b ~ true *)
      by rewrite size_tuple.
    + (* Case: b ~ false *)
      move/eqP: (IH t) => -> //=.
Qed.

Canonical off_r {n} (t: BITS n): BITS n
  := Tuple (off_rP t).

Lemma off_r_repr:
  forall n (bs: BITS n),
    andB bs (subB bs #1) = off_r bs.
Proof.
  elim=> [bs|n IHn /tupleP [b bs]].
  - (* Case: x ~ [tuple] *)
    by apply trivialBits.
  - (* Case: x ~ [tuple b & bs] *)
    case: b.
    + (* Case: b ~ true *)
      have ->: off_r [tuple of true :: bs] = [tuple of false :: bs]
        by apply: val_inj.
      by rewrite subB1 /= tuple.beheadCons
                 /andB liftBinOpCons -/andB andBB.
    + (* Case: b ~ false *)
      have ->: off_r [tuple of false :: bs] = [tuple of false :: off_r bs]
        by apply: val_inj.
      by rewrite subB1 /= tuple.beheadCons -subB1
                 /andB liftBinOpCons -/andB IHn.
Qed.

Lemma count_off_r:
  forall n (bs: BITS n), bs <> #0 ->
    count_mem true (andB bs (subB bs #1)) = (count_mem true bs) - 1.
Proof.
  move=> n bs bs_neqz.
  rewrite off_r_repr.
  elim: n bs bs_neqz=> [bs|n IHn bs] bs_neqz.
  + (* Case: n ~ 0 *)
    exfalso.
    apply bs_neqz.
    by apply trivialBits.
  + (* Case: n ~ n + 1 *)
    case/tupleP: bs bs_neqz=>b bs bs_neqz.
    case: b bs_neqz=> bs_neqz.
    - (* Case: b ~ true *)
      have ->: off_r [tuple of true :: bs] = [tuple of false :: bs]
        by apply: val_inj.
      rewrite /=.
      auto with arith.
    - (* Case: b ~ false *)
      have ->: off_r [tuple of false :: bs] = [tuple of false :: (off_r bs)]
        by apply: val_inj.
      rewrite /=.
      apply IHn.
      move=> bs_eqz.
      apply bs_neqz.
      rewrite bs_eqz //.
Qed.

Definition pop {n}(bs: BITS n): nat
  := let fix count n x :=
       if x == #0 then n
       else count (n + 1) (andB x (subB x #1))
     in count 0 bs.

Lemma pop_repr:
  forall n (bs: BITS n),
    pop bs = count_bits bs true.
Proof.
  admit.
Admitted.
*)

(** Algorithm using divide-and-conquer **)

(*
Definition pop_mask_seq {n}(k: nat): seq bool
  := let fix aux n :=
       match n with
       | 0 => [::]
       | n'.+1 => ((n' %% (2 * k)) >= k) :: aux n'
       end
     in aux n.

Lemma pop_maskP {n}(k: nat): size (pop_mask_seq (n := n) k) == n.
Proof.
  elim: n=> [|n IHn] //=.
Qed.

Canonical pop_mask {n} (k: nat): BITS n
  := Tuple (pop_maskP k).

Definition pop_nextBits {n}(bs: BITS (2^n))(k: nat) : BITS (2^n) :=
   addB (andB bs (pop_mask k)) (andB (shrBn bs k) (pop_mask k)).

Fixpoint popAux {n}(i: nat)(k: nat)(x: BITS (2^n)): BITS (2^n)
  := match i with
     | 0 => x
     | i'.+1 => popAux i' k.*2 (pop_nextBits x k)
     end.

Definition pop {n}(bs: BITS (2^n)): nat
  := toNat(popAux n 1 bs).

Fixpoint sum_tuple_seqAux {n}(bs: BITS (2^n))(k: nat): seq nat
  := match k with
     | 0 => map (fun b => (if b then 1 else 0)) bs
     | k'.+1 => let t' := sum_tuple_seqAux bs k' in
                mkseq (fun i => nth 0 t' (2 * i) + nth 0 t' (2 * i + 1)) (2 ^ (n - k))
     end.
(*
 * The i-th element of sum_tuple_seq bs k is the number of bits to 1
 * from offset i * 2^k to offset (i + 1) * 2^k
 *)
Definition sum_tuple_seq {n}(bs: BITS (2^n))(k: nat)(le_k: k <= n): seq nat
  := sum_tuple_seqAux bs k.

Lemma sum_tupleP {n}(bs: BITS (2^n))(k: nat)(le_k: k <= n):
  size (sum_tuple_seq bs k le_k) == 2^(n - k).
Proof.
  case: k le_k=> [|k] le_k.
  + (* k ~ 0 *)
    by rewrite size_map size_tuple subn0.
  + (* k ~ k.+1 *)
    by rewrite size_mkseq.
Qed.

Canonical sum_tuple {n}(bs: BITS (2^n))(k: nat)(le_k: k <= n): (2^(n - k)).-tuple nat
  := Tuple (sum_tupleP bs k le_k).

(*
 * sumn (sum_tuple (addB (andB x (pop_mask k)) (andB (shrBn x k) (pop_mask k))) k.*2)
 * (= sumn (sum_tuple f(x) k.*2))
 * = sumn (sum_tuple x k)

   sum_tuple x k [i.*2] + sum_tuple x k [i.*2 + 1]
   = sum_tuple f(x) k.*2 [i]

 * 1) Show that sum_tuple x k [i] = toNat (take k (shrB (k*i) x))
 * 2) Show that:
   toNat (take k (shrBn (k*i.*2) x)) + toNat (take k (shrBn (k*i.*2 + k) x)) (X)
   = toNat (take k.*2 (shrBn (k*i.*2) f(x)))

   Because (addB (take k bs) (take k bs')) = take k.*2 (addB bs bs'):
   X = toNat (take k.*2 (addB (shrBn (k*i.*2) x) (shrBn (k*i.*2 + k) x)))

   And:
   take k.*2 (shrBn (k*i.*2) (addB (andB x (pop_mask k)) (andB (shrBn x k) (pop_mask k)))
   = take k.*2 (addB (shrBn (k*i.*2) x) (shrBn (k*i.*2 + k) x))

   => sumn (sum_tuple bs 1) = sumn (sum_tuple (popAux n 1 bs) (2^n))
      = count_mem true bs     = pop bs
*)

Lemma pop_repr:
  forall n (bs: BITS (2 ^ n)),
    pop bs = count_mem true bs.
Proof.
  move=> n bs.
  have H: n <= n by trivial.
  have ->: pop bs = sumn (sum_tuple (popAux n 1 bs) n H)
    by admit.
  have H': 0 <= n by trivial.
  have ->: count_mem true bs = sumn (sum_tuple bs 0 H')
    by admit.
  have: forall x k, sumn (sum_tuple x k) = sumn (sum_tuple bs 1)
    -> sumn (sum_tuple (pop_nextBits x k) k.*2) = sumn (sum_tuple bs 1).
    admit.
    rewrite /popAux.
  admit.
Admitted.
*)

Definition pop_table (n: nat) := mkseq (fun i => count_mem true (fromNat (n := 2^n) i)) (2^n).

Definition pop_elem {n}(k: nat)(bs: BITS n)(i: nat): nat
  := let x := andB (shrBn bs (i * 2^k)) (dropmsb (decB (shlBn #1 (2^k)))) in
     nth 0 (pop_table (2^k)) (toNat x).

Fixpoint popAux {n}(k: nat)(bs: BITS n)(i: nat): nat :=
  match i with
  | 0 => 0
  | i'.+1 => (pop_elem k bs i') + (popAux k bs i')
  end.

Definition cardinal {n}(k: nat)(bs: BITS n): nat
  := popAux k bs (n %/ 2^k).

Lemma toNat_tcast:
  forall n m (bs: BITS n)(H: n = m), toNat (tcast H bs) = toNat bs.
Proof.
  admit.
Admitted.

Lemma toNat_catB:
  forall n1 n2 (bs: BITS n1) (bs': BITS n2), toNat (bs ## bs') = toNat bs' + (toNat bs) * 2 ^ n2.
Proof.
  admit.
Admitted.

(* TODO: merge with makeOnes? *)
Lemma makeOnes2:
  forall n k (q: k + (n - k) = n), k <= n -> decB (shlBn #1 k) = joinmsb (false, tcast q (zero (n - k) ## ones k)).
Proof.
  admit.
  (* TODO: adapt
  move=> n k q H.
  apply (toZp_inj (n := n.+1)).
  have ->: tcast q (zero (n - k) ## ones k) = fromNat (toNat (tcast q (zero (n - k) ## ones k))) by rewrite toNatK.
  rewrite toNat_tcast.
  rewrite toNat_catB.
  rewrite toNat_zero toNat_ones.
  rewrite toZp_joinmsb.
  rewrite toZp_fromNat.
  autorewrite with ZpHom.
  rewrite toZp_shlBn.
  autorewrite with ZpHom.
  rewrite !GRing.mulr_natr.
  rewrite -subn1.
  rewrite mulnC muln0 addn0.
  rewrite GRing.natrB.
  rewrite GRing.mulr1n //.
  rewrite expn_gt0 //.
  auto with arith.
  *)
Admitted.

Lemma count_low:
  forall n (bs: BITS n) k (H: n = 2 ^ k + (n - 2 ^ k)), toNat (n := n) bs < 2 ^ 2 ^ k ->
      count_mem true (fromNat (n := 2 ^ 2 ^ k) (toNat (n := n) bs))
    = count_mem true (low (2 ^ k) (tcast H bs)).
Proof.
  admit.
Admitted.

Lemma leB_andB:
  forall n (bs: BITS n) (bs': BITS n), leB (andB bs bs') bs'.
Proof.
  admit.
Admitted.

Lemma pop_elem_repr:
  forall n k i (bs: BITS n)(q: n = i.+1 * 2 ^ k + (n - i.+1 * 2 ^ k))(q': i.+1 * 2 ^ k = i * 2 ^ k + 2 ^ k)(H: i.+1 * 2 ^ k <= n),
    pop_elem k bs i = count_mem true (high (2 ^ k) (tcast q' (low (i.+1 * 2 ^ k) (tcast q bs)))).
Proof.
  move=> n k i bs q q' H1.
  rewrite /pop_elem.
  rewrite /pop_table.
  set bs' := andB (shrBn bs (i * 2 ^ k)) (dropmsb (decB (shlBn #1 (2 ^ k)))).
  have H'': toNat bs' < 2 ^ 2 ^ k.
    have ->: 2 ^ 2 ^ k = (toNat (n := n) (dropmsb (decB (shlBn #1 (2 ^ k))))).+1.
      admit.
    rewrite ltnS.
    rewrite -leB_nat.
    rewrite /bs'.
    by rewrite leB_andB.
  rewrite nth_mkseq.
  have H: n = 2 ^ k + (n - 2 ^ k).
    rewrite subnKC //.
    rewrite (leq_trans (n := i.+1 * 2 ^ k)) //.
    have {1}->: 2 ^ k = 1 * 2 ^ k by auto with arith.
    rewrite leq_mul2r.
    have ->: 0 < i.+1 by auto with arith.
    rewrite orbT //.
  have H': 2 ^ k + (n - 2 ^ k) = n by rewrite -H.
  have ->: high (2 ^ k) (tcast q' (low (i.+1 * 2 ^ k) (tcast q bs)))
  = low (2 ^ k) (tcast H (andB (shrBn bs (i * 2 ^ k)) (dropmsb (decB (shlBn #1 (2 ^ k)))))).
  case: n bs bs' q q' H1 H H' H''=> [bs|n bs] bs' q q' H1 H H' H''.
    admit.
  rewrite makeOnes2.
  apply allBitsEq=> i0 le_i0.
  have H''': i0 < n.+1.
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
  rewrite getBit_dropmsb.
  rewrite getBit_joinmsb.
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
  rewrite -ltnS.

  rewrite (ltn_trans (n := n.+1)) //.
  apply H'''.
  apply H'''.
  rewrite (leq_trans (n := i.+1 * 2 ^ k)) //.
  have {1}->: 2 ^ k = 1 * 2 ^ k by auto with arith.
  rewrite leq_mul2r.
  have ->: 0 < i.+1 by auto with arith.
  rewrite orbT //.
  apply count_low.
  apply H''.
  apply H''.
Admitted.

Lemma count_tcast:
  forall n m (bs: BITS n) (H: n = m), count_mem true (tcast H bs) = count_mem true bs.
Proof.
  admit.
Admitted.

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

Lemma count_repr:
  forall n (bs: BITS n) E, repr bs E ->
    count_mem true bs = #|E|.
Proof.
  admit.
Admitted.

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
