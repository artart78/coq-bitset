Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From CoqEAL Require Import hrel param refinements.
From Bits
     Require Import bits.
Require Import ops props.bineqs props.getbit.

Import Refinements.Op.

Local Open Scope rel_scope.

(** * Refinement relation *)

(* TODO: switch to extensional version *)

Definition Rfin {n} (bs: BITS n) E :=
  E = [ set x : 'I_n | getBit bs x ].


(** * Operations *)

(** ** TODO: cleanup *)

Lemma repr_rec:
  forall n (bs: BITS n) E b, Rfin [tuple of b :: bs] E ->
    Rfin bs [ set x : 'I_n | inord(x.+1) \in E ].
Proof.
  move=> n bs E b.
  rewrite !/Rfin -!setP !/eq_mem=> HE i.
  rewrite in_set HE !in_set inordK.
  rewrite /getBit -nth_behead //=.
  have ltn_i: i < n by apply ltn_ord.
  by auto with arith.
Qed.

Global Instance subset_repr {n : nat} : forall k, (k <= n)%N ->
    refines (@Rfin n) (decB (shlBn #1 k)) [set x : 'I_n | x < k].
Proof.
  rewrite refinesE.
  move=> k le_k.
  rewrite makeOnes2=> //.
  rewrite subnKC //.
  move=> ?.
  rewrite /Rfin -setP /eq_mem=> i.
  rewrite !in_set.
  rewrite getBit_tcast.
  rewrite getBit_catB.
  case ltn_i: (i < k).
  + (* i < k *)
    by rewrite getBit_ones.
  + (* i >= k *)
    by rewrite -fromNat0 getBit_zero.
Qed.

Lemma index_repr :
  forall n (bs: BITS n) x E, Rfin bs E -> x \in E ->
    index true bs = [arg min_(k < x in E) k].
Proof.
  elim=> [bs|n IHn /tupleP[b bs]] x E HE Hx.
  + (* n ~ 0 *)
    by move: x Hx=> [x le_x].
  + (* n ~ n.+1 *)
    case: b HE=> /= HE.
    - (* b ~ true *)
      case: arg_minP=> // i Hi Hj.
      have H: (i <= 0)%N.
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
      have HE': Rfin bs E' by apply (repr_rec n bs E false).
      case: arg_minP=> // i Hi Hj.
      rewrite (IHn bs x' E')=> //.
      case: arg_minP=> // i' Hi' Hj'.
      have H1: (i <= inord (n' := n) i'.+1)%N.
        rewrite (Hj (inord i'.+1)) // HE in_set.
        have ->: getBit [tuple of false :: bs] (inord (n' := n) i'.+1) = getBit bs i'.
          by rewrite inordK // -[i'.+1]addn1 -[n.+1]addn1 ltn_add2r ltn_ord.
        rewrite HE' in_set in Hi'.
        by apply Hi'.
      have nat_i_prednK: nat_of_ord i = i.-1.+1.
        by rewrite prednK // (gtz_E i).
      have H2: (i' <= cast_ord HpredK (inord (n' := n.-1) i.-1))%N.
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
        have ->: (i <= i'.+1)%N.
          rewrite inordK in H1.
          apply H1.
          by rewrite -[i'.+1]addn1 -[n.+1]addn1 ltn_add2r.
        have ->: (i'.+1 <= i)%N => //.
          rewrite /= inordK in H2.
          rewrite nat_i_prednK -[i'.+1]addn1 -[i.-1.+1]addn1 leq_add2r=> //.
          rewrite !prednK=> //.
          rewrite -(leq_add2r 1) !addn1 ltn_ord //.
          by rewrite (gtz_E i).
      by move/eqP: Heq ->.
Qed.

(** ** Equality *)

Local Instance eq_Finset {n} : eq_of {set 'I_n} := fun x y => x == y.

Global Instance eq_repr {n} : 
  refines (@Rfin n ==> Rfin ==> Logic.eq)%rel eqtype.eq_op eqtype.eq_op.
Proof.
  rewrite refinesE.
  move=> bs E H bs' E' H'.
  rewrite /Rfin in H, H'.
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

(** ** Membership test *)

Definition get {n}(bs: BITS n)(k: 'I_n): bool
  := (andB (shrBn bs k) #1) == #1.

Global Instance get_Bitset {n} : get_of 'I_n (BITS n) := (fun k bs => get bs k).
Global Instance get_Finset {n} : get_of 'I_n {set 'I_n} := (fun k E => k \in E).

Global Instance get_Rfin {n}: 
  refines (Logic.eq ==> @Rfin n.+1 ==> Logic.eq) get_op get_op.
Proof.
  Local Arguments get_op /.
  Local Arguments get_Finset /.
  Local Arguments get_Bitset /.

  rewrite refinesE.
  move=> k _ <- bs E HE /=.
  rewrite /get andB_mask1 getBit_shrBn addn0=> //.
  rewrite HE in_set.
  case: (getBit bs k).
  + (* getBit bs k = true *)
    by rewrite eq_refl.
  + (* getBit bs k = false *)
    by case H: (#0 == #1)=> //.
Qed.

(** ** Singleton *)

Global Instance singleton_Bitset {n} : singleton_of 'I_n (BITS n) 
  := (fun k => setBit #0 k true).
Global Instance singleton_Finset {n} : singleton_of 'I_n {set 'I_n}
  := (fun k => [set k]).

Global Instance singleton_repr {n}:
    refines (@Logic.eq 'I_n ==> @Rfin n) singleton_op singleton_op.
Proof.
  rewrite refinesE.
  move=> k _ <-.
  rewrite /Rfin -setP /eq_mem=> x.
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

(** ** Set complement  *)

Global Instance compl_Bitset {n} : compl_of (BITS n) := invB.
Global Instance compl_Finset {n} : compl_of {set 'I_n} := (@setC _).

Global Instance compl_Rfin {n}: refines (@Rfin n ==> Rfin) compl_op compl_op.
Proof.
  rewrite refinesE /Rfin=> bs E HE.
  rewrite -setP /eq_mem=> x.
  by rewrite in_setC HE !in_set getBit_liftUnOp.
Qed.

(** ** Full and empty set *)

Definition create {n} (b: bool): BITS n
  := if b then decB #0 else #0.

Global Instance full_Bitset {n} : full_of (BITS n) := create true.
Global Instance full_Finset {n} : full_of {set 'I_n} := [set : 'I_n ].

Global Instance empty_Bitset {n} : empty_of (BITS n) := create false.
Global Instance empty_Finset {n} : empty_of {set 'I_n} := set0.

Global Instance full_Rfin {n} : refines (@Rfin n) full_op full_op.
Proof.
  Local Arguments full_op /.
  Local Arguments full_Finset /.
  Local Arguments full_Bitset /.

  rewrite refinesE.
  rewrite /Rfin /= -setP /eq_mem=> x.
  rewrite !in_set.
  by rewrite -makeOnes getBit_ones=> //.
Qed.

Global Instance emptyset_repr {n} : refines (@Rfin n) empty_op empty_op.
Proof.
  rewrite refinesE //= /Rfin -setP /eq_mem=> i.
  by rewrite in_set in_set0 getBit_zero.
Qed.

(** ** Element insertion *)

Definition insert {n} k (bs: BITS n): BITS n := orB bs (shlBn #1 k).

Global Instance set_Finset {n} : set_of 'I_n {set 'I_n} := (fun k E => k |: E).
Global Instance set_Bitset {n} : set_of 'I_n (BITS n) := insert.

Lemma insert_Rfin {n}:
  refines (Logic.eq ==> @Rfin n ==> Rfin) set_op set_op.
Proof.
  rewrite refinesE.
  move=> k _ <- bs E HE /=.
  rewrite /Rfin -setP /eq_mem=> x.
  rewrite in_set getBit_set_true=> //.
  rewrite fun_if.
  case H: (x == k).
    + (* Case: x == k *)
      move/eqP: H ->.
      by rewrite eq_refl setU11.
    + (* Case: x <> k *)
      rewrite ifF=> //.
      by rewrite in_setU1 H HE in_set.
Qed.

(** ** Element removal *)

Definition remove {n}(bs: BITS n) k: BITS n
  := andB bs (invB (shlBn #1 k)).

Global Instance remove_Bitset {n} : remove_of 'I_n (BITS n) := @remove n.
Global Instance remove_Finset {n} : remove_of 'I_n {set 'I_n} := (fun A a => A :\ a).

Global Instance remove_Rfin {n}:
  refines (@Rfin n ==> Logic.eq ==> Rfin) remove_op remove_op.
Proof.
  rewrite refinesE.
  move=> bs E HE k _ <-.
  rewrite /Rfin -setP /eq_mem=> x.
  rewrite in_set getBit_set_false=> //.
  rewrite fun_if.
  case H: (x == k).
    + (* Case: x == k *)
      move/eqP: H ->.
      rewrite ifT=> //.
      by rewrite setD11.
    + (* Case: x <> k *)
      rewrite ifF=> //.
      by rewrite in_setD1 H HE in_set.
Qed.

(** ** Set intersection *)

Definition inter {n} (bs: BITS n) (bs': BITS n): BITS n
  := andB bs bs'.

Global Instance inter_Bitset {n} : inter_of (BITS n) := @inter n.
Global Instance inter_Finset {n} : inter_of {set 'I_n} := @setI _.

Global Instance inter_Rfin {n} :
  refines (@Rfin n ==> Rfin ==> Rfin) inter_op inter_op.
Proof.
  rewrite refinesE.
  move=> bs E HE bs' E' HE'.
  rewrite /Rfin -setP /eq_mem=> x.
  by rewrite in_setI /inter /andB HE HE' !in_set getBit_liftBinOp.
Qed.

(** ** Set union *)

Definition union {n} (bs: BITS n) (bs': BITS n): BITS n
  := orB bs bs'.

Global Instance union_Bitset {n} : union_of (BITS n) := @union n.
Global Instance union_Finset {n} : union_of {set 'I_n} := @setU _.

Global Instance union_repr {n}:
  refines (@Rfin n ==> Rfin ==> Rfin)%rel union_op union_op.
Proof.
  rewrite refinesE.
  move=> bs E HE bs' E' HE'.
  rewrite /Rfin -setP /eq_mem=> x.
  by rewrite in_setU /union /orB HE HE' !in_set getBit_liftBinOp.
Qed.

(** ** Set symmetric difference *)

Definition symdiff {n} (bs: BITS n) (bs': BITS n): BITS n
  := xorB bs bs'.

Global Instance symdiff_Bitset {n} : symdiff_of (BITS n) := @symdiff n.
Global Instance symdiff_Finset {n} : symdiff_of {set 'I_n} := (fun E E' =>  ((E :\: E') :|: (E' :\: E))).

Global Instance symdiff_Rfin {n}:
  refines (@Rfin n ==> Rfin ==> Rfin) symdiff_op symdiff_op.
Proof.
  rewrite refinesE.
  move=> bs E HE bs' E' HE'.
  rewrite /Rfin -setP /eq_mem=> x /=.
  rewrite in_setU !in_setD.
  rewrite /symdiff /xorB HE HE' !in_set getBit_liftBinOp=> //.
  case: (getBit bs x)=> //.
  + (* getBit bs x = true *)
    by rewrite andbT orbF Bool.xorb_true_l.
  + (* getBit bs x = false *)
    by rewrite andbF orbC orbF andbC andbT Bool.xorb_false_l.
Qed.

End BitRepr.
