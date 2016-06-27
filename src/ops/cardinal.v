Require Import mathcomp.ssreflect.ssreflect.
From CoqEAL Require Import refinements hrel.
From Bits
     Require Import bits ops axioms32 ssrextra.tuple. 
Require Import ops spec.

Import Refinements.Op.
Import Logical.Op.

(** * Cardinal through binary population count  *)

(* TODO: compute the table only once *)

Section Operations.

Variables (Bits : Type).

Context `{eq_of Bits}.
Context `{sub_of Bits}.
Context `{zero_of Bits}.
Context `{one_of Bits}.
Context `{add_of Bits}.
Context `{mul_of Bits}.
Context `{implem_of nat Bits}.
Context `{spec_of Bits nat}.

Context `{not_of Bits}.
Context `{or_of Bits}.
Context `{and_of Bits}.
Context `{xor_of Bits}.
Context `{shl_of Bits}.
Context `{shr_of Bits}.
Context `{size_of Bits}.

Variable (k: Bits).
Variable pop_table: seq Bits.

Definition pop_elem (bs: Bits)(i: nat): Bits
  := (let x := (bs >> ((implem i) * k)) && ((shl_op 1 k) - 1) in
     nth 0 pop_table (spec x))%C.

Fixpoint popAux (bs: Bits)(i: nat): Bits :=
  match i with
  | 0 => 0%C
  | i'.+1 => (pop_elem bs i' + popAux bs i')%C
  end.

Definition cardinal (bs: Bits): Bits
  := popAux bs (sizeof_op bs %/ spec k).

End Operations.

Parametricity pop_elem.
Parametricity popAux.
Parametricity cardinal.

Arguments pop_elem {_}{_}{_}{_}{_}{_}{_}{_}{_}{_} k pop_table bs i.

Definition pop_table_BITS {n} (k: nat): seq (BITS n)
  := mkseq (fun i => fromNat (count_mem true (fromNat (n := k) i)))
           (2^k).




Global Instance Int32_implem: implem_of nat Int32 := fun n => bitsToInt32 (fromNat n).
Global Instance Int32_spec: spec_of Int32 nat := fun bs => toNat (bitsFromInt32 bs).

Global Instance Bits_implem {n} : implem_of nat (BITS n) := fun n => fromNat n.
Global Instance Bits_spec {n} : spec_of (BITS n) nat := fun bs => toNat bs.

Global Instance implem_Rnative :
   refines (param.nat_R ==> Rnative)%rel Int32_implem Bits_implem.
Proof.
  rewrite refinesE=> m n Hmn.
  rewrite /Rnative/test_native/Int32_implem/Bits_implem.
  apply nat_R_eq in Hmn. subst.
  apply /eqInt32P=> //.
Qed.

Global Instance spec_Rnative:
   refines (Rnative ==> param.nat_R)%rel Int32_spec Bits_spec.
Proof.
  rewrite refinesE=> n bs Hnbs.
  rewrite /Int32_spec/Bits_spec.
  rewrite /Rnative/test_native eq_adj in Hnbs.
  move/eqP: Hnbs=> <-.
  apply param.nat_Rxx.
Qed.

Global Instance pop_elem_Rnative: 
  refines (Rnative ==> param.list_R Rnative ==> Rnative ==> param.nat_R ==> Rnative)%rel 
          pop_elem pop_elem.
Proof. param pop_elem_R. Qed.

Lemma pop_elem_Rfin:
  forall n k i (bs: BITS n)
         (q: n = i.+1 * k + (n - i.+1 * k))
         (q': i.+1 * k = i * k + k),
    i.+1 * k <= n ->
        pop_elem (@fromNat n k) (pop_table_BITS k) bs i = #(count_mem true (high k (tcast q' (low (i.+1 * k) (tcast q bs))))).
Proof.
  move=> n k i bs q q' leq_Sik.
  have le_k: k < n.+1.
    rewrite (leq_ltn_trans (n := i.+1 * k)) //.
    by rewrite -[i.+1]addn1 mulnDl mul1n -{1}[k]add0n leq_add2r.
  have H: n = k + (n - k).
    by rewrite subnKC.
  have H': k + (n - k) = n by rewrite -H.
  have H2: k < 2 ^ n.
  admit. (* XXX: probably false *)
  have H3: i * k < 2 ^ n.
  admit. (* XXX: not sure about that *)

  rewrite /pop_elem /pop_table_BITS.
  rewrite /shr_op/notations.shr_Bits/implem/Bits_implem.
  rewrite /shl_op/notations.shl_Bits.
  rewrite /mul_op/notations.mul_Bits.
  rewrite /and_op/notations.and_Bits.
  rewrite /sub_op/notations.sub_Bits/notations.sub.
  rewrite /one_op/notations.one_Bits.
  rewrite /spec/Bits_spec.
  rewrite fromNat_mulBn.
  rewrite !toNat_fromNatBounded=> //.
  rewrite subB1.
  rewrite makeOnes2=> //.
  set bs' := andB (shrBn bs (i * k)) (tcast H' (spec.zero (n - k) ## ones k)).
  have toNat_bounded: toNat bs' < 2 ^ k.
    have ltn_ones: toNat (n := n) (tcast H' (spec.zero (n - k) ## ones k)) < 2 ^ k.
      rewrite toNat_tcast toNatCat toNat_zero toNat_ones mul0n add0n
              -(ltn_add2r 1) !addn1 prednK // expn_gt0.
      by auto with arith.
    by rewrite (leq_ltn_trans (n := toNat (n := n) (tcast H' (spec.zero (n - k) ## ones k)))) //
              -leB_nat leB_andB.
  rewrite nth_mkseq=> //.

  have ->: high k (tcast q' (low (i.+1 * k) (tcast q bs)))
         = low k (tcast H (andB (shrBn bs (i * k)) (tcast H' (spec.zero (n - k) ## ones k)))).
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
Admitted.


(*
(* =pop_elem_def= *)
Definition pop_elem {n}(k: nat)(bs: BITS n)(i: nat): BITS n
  := let x := andB (shrBn bs (i * k)) (decB (shlBn #1 k)) in
     nth (zero n) (pop_table k) (toNat x).
(* =end= *)

(* =cardinal_def= *)
Fixpoint popAux {n}(k: nat)(bs: BITS n)(i: nat): BITS n :=
  match i with
  | 0 => zero n
  | i'.+1 => addB (pop_elem k bs i') (popAux k bs i')
  end.

Definition cardinal {n}(k: nat)(bs: BITS n): BITS n
  := popAux k bs (n %/ k).
(* =end= *)

Lemma count_tcast:
  forall n m (bs: BITS n) (H: n = m), count_mem true (tcast H bs) = count_mem true bs.
Proof.
  move=> n m bs H.
  by case: m / H.
Qed.

(* TODO: passing the associative/commutative proofs by hand is an
         annoyance. That's something to ponder.. *)


Lemma pop_rec:
  forall n k i (bs: BITS n)
         (q: n = i * k + (n - i * k)),
    i * k <= n -> k > 0 ->
        popAux k bs i = #(count_mem true (low (i * k) (tcast q bs))).
Proof.
  move=> n k i.
  move: i n.
  elim=> [|i IHi] n bs q le_i k_gtz.
  + (* i ~ 0 *)
    by rewrite fromNat0.
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
    rewrite pop_elem_Rfin=> //.
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
    by rewrite count_tcast count_cat fromNat_addBn addnC.
Qed.

Definition countT {n} (bs : BITS n) : nat := count_mem true bs.
Definition cardF {n} (E : {set ordinal_finType n }) := #| E |.

Global Instance count_repr {n}: refines (@Rfin n ==> Logic.eq)%rel countT cardF.
Proof.
  rewrite refinesE /countT.
  elim: n=> [bs|n IHn /tupleP[b bs]] E HE.
  + (* n ~ 0 *)
    rewrite tuple0 /cardF /= eq_card0 //.
    rewrite /eq_mem=> x.
    by move: x => [x le_x].
  + (* n ~ n.+1 *)
    rewrite /cardF HE (cardD1 ord0).
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


Global Instance cardinal_Bits {k n} : cardinal_of (BITS n) (BITS n) := cardinal k.

Global Instance cardinal_Rfin {n} k (div_k_n: k %| n)(gtz_k: k > 0):
    refines (@Rfin n ==> Logic.eq)%rel (cardinal k) (fun E => #(#|E|)).
Proof.
  rewrite refinesE.
  move=> bs E HE.
  have Hcast1: n = n %/ k * k.
    by rewrite divnK=> //.
  rewrite /cardinal pop_rec;
    try (by rewrite -?Hcast1 ?subnKC //).
  move=> Hcast0.
  have ->: low (n %/ k * k) (tcast Hcast0 bs) = tcast Hcast1 bs.
    apply allBitsEq=> i le_i.
    by rewrite getBit_low le_i !getBit_tcast.
  rewrite count_tcast.
  rewrite -[count_mem true bs]/(countT bs).
  by rewrite [countT bs]refines_eq.
Qed.
*)
