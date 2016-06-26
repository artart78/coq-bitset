Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From CoqEAL Require Import hrel param refinements.
From Bits
     Require Import bits ops axioms32 spec.notations.
Require Import ops props.bineqs props.getbit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.
Import Logical.Op.

Local Open Scope rel_scope.


Section Operations.

Variables (Bits : Type).

Context `{eq_of Bits}.
Context `{sub_of Bits}.
Context `{zero_of Bits}.
Context `{one_of Bits}.

Context `{not_of Bits}.
Context `{or_of Bits}.
Context `{and_of Bits}.
Context `{xor_of Bits}.
Context `{shl_of Bits}.
Context `{shr_of Bits}.

Definition get (k: Bits)(bs: Bits): bool
  := ((bs >> k) && 1 == 1)%C.

Definition singleton (n: Bits): Bits 
  := (shl_op 1 n)%C.

Definition compl (n: Bits): Bits 
  := (~ n)%C.

Definition create (b: bool): Bits
  := (if b then 0 - 1 else 0)%C.

Definition inter (bs bs': Bits): Bits 
  := (bs && bs')%C.

Definition union (bs bs': Bits): Bits
  := (bs || bs')%C.

Definition min (bs: Bits): Bits
  := (bs && ~ bs)%C.

Definition insert (k bs: Bits): Bits
  := (bs || (shl_op 1 k))%C.

Definition remove (bs k: Bits): Bits
  := (bs && (~ (shl_op 1 k)))%C.

Definition symdiff (bs1 bs2: Bits): Bits
  := (bs1 ^^ bs2)%C.

Definition subset (bs1 bs2: Bits): bool
  := ((bs1 && bs2) == bs1)%C.

End Operations.

Arguments get {_}{_}{_}{_}{_} k bs.
Arguments singleton {_}{_}{_} n.
Arguments compl {_}{_} n.
Arguments create {_}{_}{_}{_} b.
Arguments inter {_}{_} bs bs'.
Arguments union {_}{_} bs bs'.
Arguments min {_}{_}{_} bs.
Arguments insert {_}{_}{_}{_} k bs.
Arguments remove {_}{_}{_}{_}{_} bs k.
Arguments symdiff {_}{_} bs1 bs2.
Arguments subset {_}{_}{_} bs1 bs2.

Parametricity get. 
Parametricity singleton.
Parametricity compl.
Parametricity create.
Parametricity inter.
Parametricity union.
Parametricity min.
Parametricity insert.
Parametricity remove.
Parametricity symdiff.
Parametricity subset.

Global Instance get_Rnative: 
  refines (Rnative ==> Rnative ==> param.bool_R)%rel get get.
Proof. param (get_R (Bits_R := Rnative)). Qed.

Global Instance singleton_Rnative: 
  refines (Rnative ==> Rnative)%rel singleton singleton.
Proof. param singleton_R. Qed.

Global Instance compl_Rnative: 
  refines (Rnative ==> Rnative)%rel compl compl.
Proof. param compl_R. Qed.

Global Instance create_Rnative: 
  refines (param.bool_R ==> Rnative)%rel create create.
Proof. param create_R. Qed.

Global Instance inter_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel inter inter.
Proof. param inter_R. Qed.

Global Instance union_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel union union.
Proof. param union_R. Qed.

Global Instance min_Rnative: 
  refines (Rnative ==> Rnative)%rel min min.
Proof. param min_R. Qed.

Global Instance insert_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel insert insert.
Proof. param insert_R. Qed.

Global Instance remove_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel remove remove.
Proof. param remove_R. Qed.

Global Instance symdiff_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative)%rel symdiff symdiff.
Proof. param symdiff_R. Qed.

Global Instance subset_Rnative: 
  refines (Rnative ==> Rnative ==> bool_R)%rel subset subset.
Proof. param (subset_R (Bits_R := Rnative)). Qed.

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
      have HE': Rfin bs E' by apply (repr_rec HE).
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

Global Instance eq_Finset {n} : eq_of {set 'I_n} := fun x y => x == y.

Global Instance eq_repr {n} : 
  refines (@Rfin n ==> Rfin ==> param.bool_R)%rel eqtype.eq_op eqtype.eq_op.
Proof.
  rewrite refinesE.
  move=> bs E H bs' E' H'.
  rewrite /Rfin in H, H'.
  case Heq: (E == E').
  + (* E == E' *)
    have ->: bs == bs'; last by exact: bool_Rxx.
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

(*
Definition get {n}(bs: BITS n)(k: 'I_n): bool
  := (andB (shrBn bs k) #1) == #1.
*)


(*
Definition getBITS {n}(bs: BITS n)(k: 'I_n): bool.
  apply get with (Bits := BITS n); tc.
  exact: bs.
  exact: (fromNat k).
Qed.
*)

(* TODO: use [fun_hrel] *)
Check fun_hrel.
Definition Rord {n m}(k: BITS n)(i: 'I_m): Type := toNat k = i.

(*Global Instance get_Bitset {n} : get_of 'I_n (BITS n) := (fun k bs => get bs k).*)
Global Instance get_Bitset {n} : get_of (BITS n) (BITS n) := get. 
Global Instance get_Finset {n} : get_of 'I_n {set 'I_n} := (fun k E => k \in E).

Global Instance get_Rfin {n}: 
  refines (Rord ==> @Rfin n.+1 ==> param.bool_R) (get (Bits := BITS n.+1)) get_op.
Proof.
  Local Arguments one_op /.
  Local Arguments one_Bits /.
  Local Arguments eq_op /.
  Local Arguments eq_Bits /.
  Local Arguments get_op /.
  Local Arguments get_Finset /.
  Local Arguments get_Bitset /.

  rewrite refinesE=> bs1 k Hbs1 bs2 E HE /=.
  rewrite /get/and_op/and_Bits/shr_op/shr_Bits andB_mask1 getBit_shrBn addn0 Hbs1=> //.
  rewrite HE in_set /one_op/one_Bits/eq_op/eq_Bits.
  case: (getBit bs2 k).
  + (* getBit bs k = true *)    
    by rewrite eq_refl.
  + (* getBit bs k = false *)
    by case H: (#0 == #1)=> //.
Qed.


(** ** Singleton *)

Global Instance singleton_Bitset {n} : singleton_of (BITS n) (BITS n) 
  := (fun k => singleton k).
Global Instance singleton_Finset {n} : singleton_of 'I_n {set 'I_n}
  := (fun k => [set k]).

Global Instance singleton_repr {n}:
    refines (Rord ==> @Rfin n) singleton_op singleton_op.
Proof.
  rewrite refinesE=> bs k Hbsk.
  rewrite /Rfin -setP 
          /singleton_op/singleton_Finset/singleton_Bitset
          /singleton/one_op/one_Bits/shl_op/shl_Bits Hbsk /eq_mem=> x.
  rewrite !in_set.
  case x_eq_k: (x == k).
  + (* x == k *)
    move/eqP: x_eq_k ->.
    by rewrite getBit_shlBn_true.
  + (* x <> k *)
    rewrite getBit_shlBn_false //.
    apply not_eq_sym=> x_is_k.
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

(*
Definition create {n} (b: bool): BITS n
  := if b then decB #0 else spec.zero n.
*)

Global Instance full_Bitset {n} : full_of (BITS n) := create (Bits := BITS n) true.
Global Instance full_Finset {n} : full_of {set 'I_n} := [set : 'I_n ].

Global Instance empty_Bitset {n} : empty_of (BITS n) := create (Bits := BITS n) false.
Global Instance empty_Finset {n} : empty_of {set 'I_n} := set0.

Global Instance full_Rfin {n} : refines (@Rfin n) full_op full_op.
Proof.
  Local Arguments full_op /.
  Local Arguments full_Finset /.
  Local Arguments full_Bitset /.

  rewrite refinesE.
  rewrite /Rfin /= -setP /eq_mem=> x.
  rewrite !in_set.
  rewrite /sub_op/sub_Bits/sub/zero_op/zero_Bits.
  by rewrite subB1 -fromNat0 -makeOnes getBit_ones=> //.
Qed.

Global Instance emptyset_Rfin {n} : refines (@Rfin n) empty_op empty_op.
Proof.
  Local Arguments empty_op /.
  Local Arguments empty_Finset /.
  Local Arguments empty_Bitset /.
  Local Arguments zero_op /.
  Local Arguments zero_Bits /.
  Local Arguments create /.

  rewrite refinesE //= /Rfin -setP /eq_mem=> i.
  by rewrite in_set in_set0 /empty_op/empty_Bitset/create -fromNat0 getBit_zero.
Qed.

(** ** Element insertion *)

Global Instance set_Finset {n} : set_of 'I_n {set 'I_n} := (fun k E => k |: E).
Global Instance set_Bitset {n} : set_of (BITS n) (BITS n) := insert.

Global Instance insert_Rfin {n}:
  refines (Rord ==> @Rfin n ==> Rfin) insert set_op.
Proof.
  rewrite refinesE.
  move=> bs k Hbsk bs' E HE /=.
  rewrite /Rfin -setP /eq_mem=> x.
  rewrite /set_op/set_Finset/set_Bitset
          /insert/one_op/one_Bits/or_op/or_Bits/shl_op/shl_Bits.
  rewrite in_set Hbsk getBit_set_true=> //.
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


Global Instance remove_Bitset {n} : remove_of (BITS n) (BITS n) := remove.
Global Instance remove_Finset {n} : remove_of 'I_n {set 'I_n} := (fun A a => A :\ a).

Global Instance remove_Rfin {n}:
  refines (@Rfin n ==> Rord ==> Rfin) remove_op remove_op.
Proof.
  rewrite refinesE.
  move=> bs E HE bs' k Hbsk.
  rewrite /Rfin -setP /eq_mem=> x.
  rewrite /remove_op/remove_Bitset/remove/and_op/and_Bits/shl_op/shl_Bits Hbsk.
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

Global Instance inter_Bitset {n} : inter_of (BITS n) := inter.
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

Global Instance union_Bitset {n} : union_of (BITS n) := union.
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

Global Instance symdiff_Bitset {n} : symdiff_of (BITS n) := symdiff.
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



Global Instance subset_Bitset {n}: subset_of (BITS n) := subset.
Global Instance subset_Finset {n}: subset_of {set 'I_n} := (fun E E' => E \subset E').

Global Instance subset_Rfin {n}:
  refines (@Rfin n ==> Rfin ==> bool_R) subset_op subset_op.
Proof.
  rewrite refinesE=> bs E HE bs' E' HE'.
  rewrite /subset_op/subset_Bitset/subset_Finset/subset.
  have ->: E \subset E' = (E :&: E' == E).
  apply/setIidPl/eqP=> //=.
  eapply refinesP; tc.
Qed.
