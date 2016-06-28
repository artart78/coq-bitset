Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset binomial.
From Bits
     Require Import bits extraction.axioms32.

Require Import repr_op.

Definition enumNext (x: Int32) := (* 111001100 *)
  let smallest := keep_min x in(* 000000100 *)
  let ripple := add smallest x in  (* 111010000 *)
  let ones := lsr (lxor x ripple) (add (toInt 2) (ntz x)) in
  lor ripple ones.

Definition set_isNext (S: {set 'I_wordsize}) x := (x \notin S) && [exists y, (y \in S) && (y < x)].

Definition set_next (S: {set 'I_wordsize}) e := [arg min_(x < e | set_isNext S x) x].

Definition set_min (S: {set 'I_wordsize}) e := [arg min_(x < e in S) x].

Definition enumNext_set (S: {set 'I_wordsize}) e f :=
  let s_min := set_min S e in
  let s_next := set_next S in
  [set s_next f] :|: [set x in S | x > s_next f] :|: (if s_next f >= s_min + 2 then [set x in 'I_wordsize | x <= (s_next f - s_min - 2)] else set0).

(* TODO: move to ops/*.v *)
Lemma srn_repr_1:
  forall n (bs: BITS n) E (H: n.-1.+1 = n), spec.repr bs E -> forall k,
    spec.repr (shrBn bs k) [set i : 'I_n | i < n - k & cast_ord H (@inord n.-1 (i + k)) \in E].
Proof.
  move=> n bs E H HE.
  elim=> [|k Hk].
  + (* k = 0 *)
    rewrite /=.
    have ->: [set i : 'I_n | i < n - 0 & cast_ord H (inord (i + 0)) \in E] = E.
      apply/setP=> x; rewrite !inE.
      rewrite subn0 ltn_ord /=.
      rewrite addn0.
      have ->: cast_ord H (inord x) = x.
        apply ord_inj.
        rewrite nat_cast_ord inordK //.
        by rewrite H.
      rewrite //.
    rewrite //.
  + (* k~k.+1 *)
    rewrite /shrBn /= -/shrBn.
    have ->: [set i : 'I_n | i < n - k.+1 & cast_ord H (inord (i + k.+1)) \in E]
           = [set i : 'I_n | i < n.-1 & cast_ord H (@inord n.-1 i.+1) \in [set i : 'I_n | i < n - k & cast_ord H (inord (i + k)) \in E]].
      apply/setP=> x; rewrite !inE.
      case Hx: (x < n.-1)=> /=.
      + (* x < n.-1 *)
        have ->: (x < n - k.+1) = (@inord n.-1 x.+1 < n - k).
          rewrite inordK=> //.
          rewrite -[k.+1]addn1.
          rewrite subnDA.
          rewrite ltn_subRL.
          by rewrite addnC addn1.
        apply andb_id2l=> _.
        rewrite -[k.+1]addn1 -[x.+1]addn1.
        have ->: x + (k + 1) = @inord n.-1 (x + 1) + k.
          rewrite inordK.
          by rewrite -[x + 1 + k]addnA [k + 1]addnC.
          by rewrite -[n.-1.+1]addn1 ltn_add2r.
        rewrite //=.
      + (* x >= n.-1 *)
        have ->: x < n - k.+1 = false.
          rewrite ltnNge.
          apply negbF.
          apply (leq_trans (n := n.-1)).
          by rewrite -subn1 leq_sub2l.
          by rewrite leqNgt Hx.
        by rewrite /=.
    by apply shift.sr_repr.
Qed.

(* TODO: move somewhere *)
Lemma natural_repr_toInt: forall v, natural_repr (toInt v) v.
Proof.
  move=> v.
  apply/existsP.
  exists #v.
  rewrite eq_refl andbT.
  rewrite toInt_def /native_repr.
  by apply/eqInt32P.
Qed.

(* TODO: move to repr_op *)
Lemma srn_repr:
  forall i E s, s <= wordsize -> machine_repr i E ->
    machine_repr (lsr i (toInt s)) [set i : 'I_wordsize | i < wordsize - s & @inord wordsize.-1 (i + s) \in E].
Proof.
  move=> i E s Hs [bv [r_native r_set]].
  exists (shrBn bv s); split.
  apply lsr_repr=> //.
  apply natural_repr_toInt.
  have H: wordsize.-1.+1 = wordsize by trivial.
  have ->: [set i0 : 'I_wordsize | i0 < wordsize - s & inord (i0 + s) \in E]
         = [set i0 : 'I_wordsize | i0 < wordsize - s & cast_ord H (inord (i0 + s)) \in E].
    apply/setP=> x; rewrite !inE.
    apply andb_id2l=> _.
    have {1}->: inord (x + s) = (cast_ord H (inord (x + s))).
      apply ord_inj.
      by rewrite nat_cast_ord.
    rewrite //.
  by apply srn_repr_1.
Qed.

Lemma addB_zero_tt {n} (bs: BITS n.+1):
  addB [tuple of true :: spec.zero n.+1] [tuple of true :: bs]
= [tuple of false :: (addB [tuple of true :: spec.zero n] bs)].
Proof.
  apply toNat_inj.
  rewrite toNat_addB.
  rewrite /=.
  have ->: toNat [tuple of false :: addB [tuple of true :: nseq n false] bs]
         = (toNat (addB [tuple of true :: nseq n false] bs)).*2.
    by rewrite /toNat /= add0n.
  rewrite toNat_addB.
  rewrite -muln2.
  rewrite div.muln_modl=> //.
  have ->: toNat [tuple of true :: spec.zero n.+1] = 1 + (toNat [tuple of spec.zero n.+1]).*2 by trivial.
  have ->: toNat [tuple of true :: spec.zero n] = 1 + (toNat (spec.zero n)).*2 by trivial.
  have ->: toNat [tuple of true :: bs] = 1 + (toNat bs).*2 by trivial.
  rewrite expnSr.
  rewrite !toNat_zero.
  rewrite double0 addn0.
  rewrite -muln2 //.
Qed.

Lemma addB_zero_tf {n} (bs: BITS n.+1):
  addB [tuple of true :: spec.zero n.+1] [tuple of false :: bs]
= [tuple of true :: bs].
Proof.
  apply toNat_inj.
  rewrite toNat_addB.
  have ->: toNat [tuple of true :: spec.zero n.+1] = 1 + (toNat (spec.zero n.+1)).*2 by trivial.
  rewrite toNat_zero double0 addn0.
  have ->: toNat [tuple of false :: bs] = (toNat bs).*2 by trivial.
  have ->: toNat [tuple of true :: bs] = 1 + (toNat bs).*2 by trivial.
  rewrite div.modn_small //.
  rewrite -addn1.
  rewrite addnC addnA.
  have ->: 1 + 1 = 2 by trivial.
  rewrite -muln2.
  rewrite -{1}[2]mul1n.
  rewrite -mulnDl.
  rewrite expnSr.
  rewrite leq_mul2r.
  rewrite addnC addn1.
  by rewrite toNatBounded.
Qed.

Definition set_isNext_g {n} (S: {set 'I_n.+1}) y x := (y \notin S) && (y >= x).

Definition set_next_g {n} (S: {set 'I_n.+1}) f x := [arg min_(y < f | set_isNext_g S y x) y].

Lemma ripple_repr_1':
  forall n (bs: BITS n.+1) E f, spec.repr bs E -> set_isNext_g E f (@ord0 n) ->
    spec.repr (addB [tuple of true :: spec.zero n] bs) ((set_next_g E f (@ord0 n)) |: [set y in E | y > set_next_g E f (@ord0 n)]).
Proof.
  elim=> [|n IHn] /tupleP[b bs] E f Hbs HE.
  + (* n = 1 *)
    have Hf: f = ord0 by apply ord_inj; elim f; elim.
    rewrite (tuple0 bs) /=.
    rewrite /adcB /adcBmain /=.
    rewrite !tuple.theadCons /=.
    rewrite /joinlsb /=.
    case: b Hbs=> Hbs.
    + rewrite !tuple.theadCons !tuple.beheadCons /=.
      rewrite /spec.repr /=.
      apply/setP=> x.
      have Hx: x = ord0 by apply ord_inj; elim x; elim.
      rewrite !inE /getBit Hx /=.
      have ->: (ord0 == set_next_g E f 0) = false.
        apply/eqP=> Habs.
        rewrite /set_next_g in Habs.
        move: Habs.
        case: arg_minP=> //.
        move=> i Hi Hmin Hi'.
        rewrite -Hi' /set_isNext_g /= leqnn andbT in Hi.
        move: Hbs=> /setP /(_ ord0).
        rewrite inE /getBit /= => Habs.
        by rewrite Habs in Hi.
      rewrite /=.
      by rewrite ltn0 andbF.
    + rewrite !tuple.theadCons !tuple.beheadCons /=.
      rewrite /spec.repr /=.
      apply/setP=> x.
      have Hx: x = ord0 by apply ord_inj; elim x; elim.
      rewrite !inE /getBit Hx /=.
      have ->: ord0 == set_next_g E f 0.
        rewrite /set_next_g.
        case: arg_minP=> //.
        move=> i Hi Hmin.
        apply/eqP.
        apply ord_inj.
        rewrite /=.
        apply/eqP.
        rewrite eq_sym -leqn0.
        apply (Hmin ord0).
        by rewrite Hf in HE.
      by rewrite /=.
  + (* n.+1 ~ n.+2 *)
    case: b Hbs=> Hbs.
    + rewrite addB_zero_tt.
      have Hbs': ord0 \in E.
        move: Hbs=> /setP /(_ ord0) ->.
        by rewrite inE /getBit.
      set E' := [set x : 'I_n.+1 | inord(x.+1) \in E ].
      set f' := @inord n f.-1.
      have HE': spec.repr bs E'.
        by apply (spec.repr_rec (b := true)).
      have Hf': set_isNext_g E' f' (@ord0 n.+1).
        rewrite /set_isNext_g.
        rewrite /= leq0n andbT.
        apply/negP=> Habs.
        rewrite inE in Habs.
        have Hf1: f > 0.
          rewrite lt0n.
          apply/negP=> /eqP Habs'.
          have Habs'': f = ord0 by apply ord_inj.
          rewrite Habs'' in HE.
          move: HE=> /andP[Habs''' _].
          by rewrite Hbs' in Habs'''.
        have Hf': inord f'.+1 = f.
          rewrite inordK.
          rewrite prednK=> //.
          apply ord_inj.
          by rewrite inordK.
          apply (leq_trans (n := f)).
          rewrite -subn1.
          rewrite -{2}[nat_of_ord f]subn0.
          apply ltn_sub2l=> //.
          by rewrite -ltnS.
        rewrite Hf' in Habs.
        move: HE=> /andP [HE _].
        by rewrite Habs in HE.
      move: (IHn bs E' f' HE' Hf')=> /setP IHn'.
      apply/setP=> i; rewrite !inE.
      case Hi: (i == ord0).
      + move: Hi=> /eqP ->.
        rewrite /getBit /=.
        rewrite ltn0 andbF orbF.
        apply/eqP.
        rewrite /set_next_g.
        case: arg_minP=> //.
        move=> i0 Hi0 Hmin.
        move=> Habs.
        rewrite -Habs in Hi0.
        move: Hi0=> /andP[Habs' _].
        by rewrite Hbs' in Habs'.
      + move: Hi=> /eqP Hi''.
        have Hi': i > 0.
          rewrite lt0n.
          apply/eqP=> H.
          have Habs: i = ord0 by apply ord_inj.
          by rewrite Habs in Hi''.
        have Hi''': i.-1 < i.
          rewrite -subn1.
          rewrite -{2}[nat_of_ord i]subn0.
          apply ltn_sub2l=> //.
        have ->: i = inord i.-1.+1.
          apply ord_inj.
          rewrite inordK.
          rewrite prednK=> //.
          by rewrite prednK=> //.
        have ->: getBit [tuple of false :: addB [tuple of true :: spec.zero n] bs] (@inord n.+1 i.-1.+1)
               = getBit (addB [tuple of true :: spec.zero n] bs) i.-1.
          rewrite /getBit inordK=> //.
          by rewrite prednK=> //.
        move: (IHn' (inord i.-1))=> IHn''.
        rewrite !inE /= inordK in IHn''.
        rewrite -IHn''.
        have Hnext: set_next_g E f 0 = inord (set_next_g E' f' 0).+1.
          rewrite /set_next_g.
          case: arg_minP=> //.
          move=> i0 Hi0 Hi0'.
          case: arg_minP=> //.
          move=> i1 Hi1 Hi1'.
          apply ord_inj.
          apply/eqP.
          rewrite eqn_leq.
          apply/andP; split.
          apply (Hi0' (inord i1.+1))=> //.
          rewrite /set_isNext_g leq0n andbT.
          rewrite /set_isNext_g leq0n andbT in Hi1.
          apply/negP=> Habs.
          have Habs': i1 \in E'.
            by rewrite inE.
          by rewrite Habs' in Hi1.
          rewrite inordK.
          have Hi0'': i0 > 0.
            rewrite lt0n.
            apply/eqP=> Habs.
            have Hi0'': i0 = ord0 by apply ord_inj.
            rewrite Hi0'' in Hi0.
            move: Hi0=> /andP [Habs' _].
            by rewrite Hbs' in Habs'.
          have Hok: i1 <= @inord n i0.-1.
            apply Hi1'.
            rewrite /set_isNext_g leq0n andbT.
            rewrite /set_isNext_g leq0n andbT in Hi0.
            apply/negP=> Habs.
            move: Hi0=> /negP Hi0.
            apply Hi0.
            rewrite inE inordK prednK in Habs=> //.
            by rewrite inord_val in Habs.
            by rewrite -ltnS.
          apply (leq_ltn_trans (n := @inord n i0.-1))=> //.
          rewrite inordK=> //.
          rewrite -subn1.
          rewrite -{2}[nat_of_ord i0]subn0.
          apply ltn_sub2l=> //.
          rewrite prednK=> //.
          rewrite -ltnS=> //.
          rewrite -addn1 -[n.+2]addn1.
          rewrite leq_add2r=> //.
        have ->: (inord i.-1.+1 == set_next_g E f 0) = (inord i.-1 == set_next_g E' f' 0).
          rewrite Hnext.
          apply/eqP.
          case H: (inord i.-1 == set_next_g E' f' 0).
          + move/eqP: H=> H.
            apply ord_inj.
            rewrite !inordK=> //.
            apply/eqP.
            rewrite eqSS.
            rewrite -H.
            rewrite inordK=> //.
            apply (leq_trans (n := i))=> //.
            rewrite -ltnS=> //.
            rewrite -[(set_next_g E' f' 0).+1]addn1 -[n.+2]addn1.
            by rewrite ltn_add2r.
            rewrite prednK=> //.
          + move/eqP: H=> H.
            move=> Habs.
            have Habs': inord i.-1 = set_next_g E' f' 0.
              apply ord_inj.
              rewrite inordK.
              apply/eqP.
              rewrite -(eqn_add2r 1).
              rewrite !addn1.
              apply/eqP.
              have ->: i.-1.+1 = @inord n.+1 i.-1.+1.
                rewrite inordK=> //.
                by rewrite prednK.
              rewrite Habs.
              rewrite inordK=> //.
              by rewrite -[(set_next_g E' f' 0).+1]addn1 -[n.+2]addn1 ltn_add2r.
              apply (leq_trans (n := i))=> //.
              rewrite -ltnS=> //.
            by rewrite Habs' in H.
        have ->: (set_next_g E f 0 < @inord n.+1 i.-1.+1) = (set_next_g E' f' 0 < i.-1).
          rewrite Hnext.
          rewrite !inordK.
          rewrite -addn1 -[i.-1.+1]addn1.
          by rewrite leq_add2r.
          rewrite prednK=> //.
          rewrite -addn1 -[n.+2]addn1.
          by rewrite leq_add2r.
        rewrite //.
        apply (leq_trans (n := i)).
        rewrite -subn1.
        rewrite -{2}[nat_of_ord i]subn0.
        apply ltn_sub2l=> //.
        by rewrite -ltnS.
    + rewrite addB_zero_tf.
      have Hbs': ord0 \notin E.
        move: Hbs=> /setP /(_ ord0) Hbs.
        rewrite Hbs.
        by rewrite inE /getBit /=.
      have ->: set_next_g E f (@ord0 n.+1) = @ord0 n.+1.
        rewrite /set_next_g.
        case: arg_minP=> //.
        move=> i Hi Hmin.
        apply ord_inj.
        rewrite /=.
        apply/eqP.
        rewrite -leqn0.
        apply (Hmin ord0).
        rewrite /set_isNext_g /= leqnn.
        by rewrite Hbs'.
      apply/setP=> x; rewrite !inE.
      case Hx: (x == ord0).
      + move: Hx=> /eqP ->.
        by rewrite /getBit.
      + have Hx': 0 < x.
          rewrite lt0n.
          apply/eqP=> Habs.
          have Habs': x = ord0.
            by apply ord_inj.
          by rewrite Habs' in Hx.
        rewrite /= Hx'.
        rewrite andbT /=.
        move: Hbs=> /setP /(_ x) ->.
        rewrite inE.
        rewrite /getBit /=.
        have ->: x = inord x.-1.+1.
          apply ord_inj.
          rewrite inordK prednK=> //.
        rewrite inordK //.
        rewrite prednK=> //.
Qed.

Lemma splitAt {n} (bs: BITS n) x (Hcast: n = x + (n - x)):
  bs = tcast (esym Hcast) ((high (n - x) (tcast Hcast bs)) ## (low x (tcast Hcast bs))).
Proof.
  apply allBitsEq=> i Hi.
  rewrite getBit_tcast.
  rewrite getBit_catB.
  rewrite getBit_low getBit_high.
  rewrite getBit_tcast.
  case Hx: (i < x)=> //.
  rewrite subnK=> //.
  by rewrite leqNgt Hx.
Qed.

Lemma addB_catB {n} (bs: BITS n) bs' x (Hcast: n = x + (n - x)):
  addB (tcast (esym Hcast) (high (n - x) (tcast Hcast bs') ## spec.zero x))
       (tcast (esym Hcast) (high (n - x) (tcast Hcast bs) ## low x (tcast Hcast bs)))
= tcast (esym Hcast) ((addB (high (n - x) (tcast Hcast bs')) (high (n - x) (tcast Hcast bs))) ## low x (tcast Hcast bs)).
Proof.
  apply toNat_inj.
  rewrite toNat_addB.
  rewrite !toNat_tcast.
  rewrite !toNatCat.
  rewrite -fromNat0 toNat_fromNat.
  rewrite toNat_addB.
  have: (toNat (low x (tcast Hcast bs))) < 2 ^ x by apply toNatBounded.
  move: (toNat (high (n - x) (tcast Hcast bs')))=> n1.
  move: (toNat (high (n - x) (tcast Hcast bs)))=> n2.
  move: (toNat (low x (tcast Hcast bs)))=> n3 H.
  rewrite div.mod0n addn0.
  rewrite addnA -mulnDl.
  rewrite div.muln_modl.
  have Hx: x <= n by rewrite Hcast -{1}[x]addn0 leq_add2l.
  rewrite -expnD subnK=> //.
  move: (n1 + n2)=> n4.
  rewrite (div.divn_eq n4 (2 ^ (n - x))).
  rewrite mulnDl.
  rewrite -mulnA.
  rewrite -expnD subnK=> //.
  rewrite -addnA.
  rewrite !div.modnMDl.
  rewrite ![div.modn _ (2 ^ n)]div.modn_small //.
  have ->: 2 ^ n = 2 ^ (n - x) * 2 ^ x by rewrite -expnD subnK.
  rewrite ltn_mul2r.
  apply/andP; split.
  rewrite expn_gt0=> //.
  rewrite div.ltn_mod expn_gt0 //.
  apply (leq_trans (n := div.modn n4 (2 ^ (n - x)) * 2 ^ x + 2 ^ x)).
  rewrite ltn_add2l //.
  have {2}->: 2 ^ x = 1 * 2 ^ x by rewrite mul1n.
  rewrite -mulnDl.
  have ->: 2 ^ n = 2 ^ (n - x) * 2 ^ x by rewrite -expnD subnK.
  rewrite leq_mul2r.
  apply/orP; right.
  rewrite addn1.
  rewrite div.ltn_mod.
  by rewrite expn_gt0.
  by rewrite expn_gt0.
Qed.

Lemma addB_tcast m n b1 b2 (Hcast: m = n): addB (tcast Hcast b2) b1 = tcast Hcast (addB b2 (tcast (esym Hcast) b1)).
Proof.
  apply toNat_inj.
  rewrite toNat_tcast.
  rewrite !toNat_addB.
  rewrite !toNat_tcast.
  move: (toNat b2 + toNat b1)=> x.
  clear b1 b2.
  by rewrite Hcast.
Qed.

Lemma ripple_repr_1:
  forall n (bs: BITS n.+1) bs' E x f, spec.repr bs E -> spec.repr bs' [set x] -> set_isNext_g E f x ->
    spec.repr (addB bs' bs) ((set_next_g E f x) |: [set y in E | y < x] :|: [set y in E | y > set_next_g E f x]).
Proof.
  move=> n bs bs' E x f Hbs Hbs' Hx.
  have Hcast: n.+1 = x + (n.+1 - x).
    rewrite subnKC=> //.
    by apply ltnW.
  rewrite (splitAt bs' x).
  have ->: low x (tcast Hcast bs') = spec.zero x.
    apply allBitsEq=> i Hi.
    rewrite getBit_low -fromNat0 getBit_zero getBit_tcast Hi.
    move: Hbs'=> /setP /(_ (inord i)) Hbs'.
    rewrite !inE /= inordK in Hbs'=> //.
    rewrite -Hbs'.
    apply/eqP=> Habs.
    have Habs': i = x.
      rewrite -Habs inordK=> //.
      apply (ltn_trans (n := x))=> //.
    by rewrite Habs' ltnn in Hi.
    apply (ltn_trans (n := x))=> //.
  rewrite (splitAt bs x).
  rewrite addB_catB.
  apply/setP=> i; rewrite !inE.
  rewrite getBit_tcast getBit_catB.
  move: Hbs=> /setP Hbs.
  move: Hbs'=> /setP Hbs'.
  case Hi: (i < x).
  + (* i < x *)
    rewrite getBit_low Hi getBit_tcast andbT.
    rewrite [(i \in E) && (set_next_g E f x < i)]andbC.
    rewrite -orbA.
    rewrite andKb.
    have ->: (i == set_next_g E f x) = false.
      apply/eqP=> Habs.
      have Habs': set_next_g E f x >= x.
        rewrite /set_next_g.
        case: arg_minP=> //.
        by move=> i0 /andP[_ Habs'] _.
      have Habs'': i < i.
        rewrite -Habs in Habs'.
        apply (leq_trans (n := x))=> //.
      by rewrite ltnn in Habs''.
    by rewrite (Hbs i) inE.
  + (* i >= x *)
    have Hcast2: (n - x).+1 = n.+1 - x.
      rewrite -subSn=> //.
      by rewrite -ltnS.
    have Hbs'1: high (n.+1 - x) (tcast Hcast bs') = tcast Hcast2 [tuple of true :: spec.zero (n - x)].
      apply allBitsEq=> i0 Hi0.
      rewrite getBit_high !getBit_tcast.
      case: i0 Hi0=> [Hi0|i0 Hi0].
      + rewrite add0n /getBit /=.
        move: (Hbs' x)=> Hbs'1.
        by rewrite !inE eq_refl /getBit in Hbs'1.
      + rewrite {2}/getBit /=.
        rewrite nth_nseq if_same.
        move: (Hbs' (inord (i0.+1 + x)))=> Hbs'1.
          rewrite !inE in Hbs'1.
          have Hi0': (inord (i0.+1 + x) == x) = false.
            apply/negP=> /eqP Habs.
            have Habs': i0.+1 + x = nat_of_ord x.
              rewrite -{2}Habs inordK=> //.
              rewrite addnC -ltn_subRL=> //.
            move: Habs'=> /eqP Habs'.
            rewrite gtn_eqF in Habs'=> //.
            rewrite -{1}[nat_of_ord x]add0n.
            rewrite ltn_add2r=> //.
          rewrite Hi0' in Hbs'1.
          rewrite Hbs'1.
          rewrite /getBit inordK //.
          rewrite addnC -ltn_subRL //.
    rewrite Hbs'1.
    rewrite andbF orbF.
    set E' := [set i in 'I_(n - x).+1 | inord (i + x) \in E].
    set f' := @inord (n - x) (f - x).
    set bs1 := tcast (esym Hcast2) (high (n.+1 - x) (tcast Hcast bs)).
    have Hlt: forall y, y < n.+1 -> x < n.+1 -> y - x < (n - x).+1.
      move=> y Hy.
      rewrite -[(n - x).+1]subSn.
      by rewrite ltn_sub2r.
      by rewrite -ltnS.
    have Hbs1: spec.repr bs1 E'.
      apply/setP=> j; rewrite !inE /=.
      rewrite getBit_tcast getBit_high getBit_tcast.
      rewrite (Hbs (inord (j + x))) inE /getBit inordK=> //.
      rewrite addnC -ltn_subRL subSn=> //.
      by rewrite -ltnS.
    have Hf': set_isNext_g E' f' 0.
      rewrite /set_isNext_g.
      rewrite leq0n andbT.
      move: Hx=> /andP[Hx' Hx''].
      apply/negP=> Habs.
      rewrite inE /= in Habs.
      have Habs': inord (f' + x) = f.
        rewrite inordK.
        apply ord_inj.
        rewrite inordK subnK=> //.
        rewrite (Hlt f)=> //.
      rewrite Habs' in Habs.
      by rewrite Habs in Hx'.
    have Hf'2: set_next_g E' f' 0 = inord ((set_next_g E f x) - x).
      rewrite /set_next_g.
      apply ord_inj.
      rewrite inordK.
      case: arg_minP=> //.
      move=> i0 /andP [Hi0 _] Hi0'.
      case: arg_minP=> //.
      move=> i1 /andP [Hi1 Hi1''] Hi1'.
      apply/eqP.
      rewrite eqn_leq.
      apply/andP; split.
      + have ->: i1 - x = nat_of_ord (@inord (n - x) (i1 - x)).
          rewrite inordK //.
          rewrite (Hlt i1)=> //.
        apply (Hi0' (inord (i1 - x))).
        rewrite /set_isNext_g leq0n andbT.
        rewrite inE /= inordK.
        rewrite subnK=> //.
        by rewrite inord_val Hi1.
        rewrite (Hlt i1)=> //.
      + rewrite leq_subLR.
        have Hxi0: x + i0 < n.+1.
          apply (leq_trans (n := x + (n - x).+1)).
          rewrite ltn_add2l=> //.
          rewrite -subSn.
          rewrite subnKC=> //.
          rewrite ltnW=> //.
          rewrite -ltnS=> //.
        have ->: x + i0 = nat_of_ord (@inord n (x + i0)).
          rewrite inordK //.
        apply (Hi1' (@inord n (x + i0))).
        rewrite /set_isNext_g.
        rewrite inE /= addnC in Hi0.
        rewrite Hi0 /=.
        rewrite inordK=> //.
        by rewrite leq_addr=> //.
      rewrite (Hlt [arg min_(y < f | set_isNext_g E y x) y])=> //.
    move: (ripple_repr_1' (n - x) bs1 E' f' Hbs1 Hf')=> /setP /(_ (inord (i - x))) H.
    rewrite !inE /= in H.
    have ->: getBit (addB (tcast Hcast2 [tuple of true :: spec.zero (n - x)])
        (high (n.+1 - x) (tcast Hcast bs))) (i - x) = getBit (addB [tuple of true :: spec.zero (n - x)] bs1) (@inord (n - x) (i - x)).
      rewrite /bs1.
      move: (high (n.+1 - x) (tcast Hcast bs))=> b1.
      move: ([tuple of true :: spec.zero (n - x)])=> b2.
      rewrite addB_tcast getBit_tcast /getBit inordK //.
      rewrite (Hlt i)=> //.
    rewrite -H.
    rewrite !Hf'2.
    have ->: (@inord (n - x) (i - x) == inord (set_next_g E f x - x)) = (i == set_next_g E f x).
      apply/eqP.
      case Hi': (i == set_next_g E f x).
      + move: Hi'=> /eqP Hi'.
        by rewrite Hi'.
      + move: Hi'=> /eqP Hi'.
        move=> Habs.
        have Habs': i = set_next_g E f x.
          apply ord_inj.
          have ->: nat_of_ord i = nat_of_ord (@inord (n - x) (i - x)) + x.
            rewrite inordK.
            rewrite subnK=> //.
            by rewrite leqNgt Hi.
            rewrite (Hlt i)=> //.
        rewrite Habs.
        rewrite inordK.
        rewrite subnK=> //.
        rewrite /set_next_g.
        case: arg_minP=> //.
        by move=> i0 /andP[_ Habs'] _.
        rewrite (Hlt (set_next_g E f x))=> //.
      by rewrite Habs' in Hi'.
    have ->: (@inord n (@inord (n - x) (i - x) + x) \in E) = (i \in E).
      rewrite inordK.
      rewrite subnK.
      by rewrite inord_val.
      by rewrite leqNgt Hi.
      by rewrite (Hlt i).
    rewrite !inordK.
    have ->: (set_next_g E f x - x < i - x) = (set_next_g E f x < i).
      case Hi': (set_next_g E f x < i).
      + rewrite ltn_sub2r=> //.
        move: Hi'.
        rewrite /set_next_g.
        case: arg_minP=> //.
        move=> i0 /andP[_ Hi0] Hmin Hi0'.
        apply (leq_ltn_trans (n := i0))=> //.
      + apply/negP=> Habs.
        have Habs': set_next_g E f x < i.
          have ->: nat_of_ord (set_next_g E f x) = set_next_g E f x - x + x.
            rewrite subnK=> //.
            rewrite /set_next_g.
            case: arg_minP=> //.
            by move=> i0 /andP[_ Hi0] _.
          have ->: nat_of_ord i = i - x + x.
            rewrite subnK=> //.
            by rewrite leqNgt Hi.
          by rewrite ltn_add2r Habs.
        by rewrite Habs' in Hi'.
    rewrite //.
    rewrite (Hlt i)=> //.
    rewrite (Hlt (set_next_g E f x))=> //.
Qed.

Lemma ripple_repr:
  forall i j S x f, machine_repr i S -> machine_repr j [set x] -> set_isNext_g S f x ->
    machine_repr (add j i) ((set_next_g S f x) |: [set y in S | y < x] :|: [set y in S | y > set_next_g S f x]).
Proof.
  move=> i j S x f [bv [r_native r_set]] [bv' [r_native' r_set']] Hx.
  exists (addB bv' bv); split.
  apply add_repr=> //.
  by apply ripple_repr_1.
Qed.

(* TODO: move from queens to somewhere else *)
Lemma ladd_repr:
  forall x y, add (toInt x) (toInt y) = toInt (x + y).
Admitted.

Lemma min_ripple_repr i (S: {set 'I_wordsize}) e (He: e \in S) f (Hf: set_isNext S f):
  machine_repr i S ->
  machine_repr (add (keep_min i) i) (set_next S f |: [set x in S | set_next S f < x]).
Proof.
  have HS: set_next S f = set_next_g S f (set_min S e).
    rewrite /set_next /set_next_g.
    rewrite /arg_min.
    rewrite (eq_pick (Q := [pred i0 | set_isNext_g S i0 (set_min S e) & [
               forall (j | set_isNext_g S j (set_min S e)),
                 i0 <= j]])) //.
    move=> x /=.
    have Heq: forall x, [exists y, (y \in S) && (y < x)] = (set_min S e < x).
      move=> x0.
      rewrite /set_min.
      case: arg_minP=> //= j Hj Hj'.
      case Hx: (j < x0).
      + apply/existsP.
        exists j.
        by rewrite Hj.
      + apply negbTE; rewrite negb_exists.
        apply/forallP=> y.
        rewrite negb_and.
        case Hy: (y \in S)=> //=.
        + move: (Hj' y Hy)=> Hy'.
          rewrite -leqNgt.
          apply (leq_trans (n := j))=> //.
          by rewrite leqNgt Hx.
    rewrite /set_isNext Heq.
    have Hhandy: forall y, (y \notin S) && (set_min S e < y) = (y \notin S) && (set_min S e <= y).
      move=> y.
      apply andb_id2l=> Hy.
      rewrite [set_min S e <= y]leq_eqVlt.
      have Habs: set_min S e \in S.
        rewrite /set_min.
        case: arg_minP=> //.
      have ->: (nat_of_ord (set_min S e) == nat_of_ord y) = false.
        apply negbTE.
        apply/eqP=> Habs'.
        have Habs'': set_min S e = y by apply ord_inj.
        rewrite Habs'' in Habs.
        by rewrite Habs in Hy.
      by rewrite /=.
    have ->: [forall (j | (j \notin S) && [exists y, (y \in S) && (y < j)]), x <= j]
           = [forall (j | (j \notin S) && (set_min S e <= j)), x <= j].
      apply eq_forallb=> y.
      rewrite Heq.
      by rewrite Hhandy.
    rewrite /set_isNext_g.
    rewrite Hhandy.
    rewrite //.
  have ->: (set_next S f |: [set x0 in S | set_next S f < x0]) = ((set_next_g S f (set_min S e)) |: [set y in S | y < (set_min S e)] :|: [set y in S | y > set_next_g S f (set_min S e)]).
    have ->: [set y in S | y < set_min S e] = set0.
      apply/setP=> x; rewrite !inE.
      rewrite /set_min.
      case: arg_minP=> //.
      move=> j Hj /(_ x) Hj'.
      case Hx: (x \in S); rewrite andbC.
      rewrite andbT.
      apply negbTE.
      rewrite -leqNgt.
      by apply Hj'.
      by rewrite andbF.
    by rewrite setU0 HS.
  move=> H.
  apply ripple_repr=> //.
  apply keep_min_repr=> //.
  rewrite /set_isNext_g.
  move: Hf=> /andP [Hf1 /existsP [y /andP [Hy1 Hy2]]].
  apply/andP; split=> //.
  apply (leq_trans (n := y))=> //.
  rewrite /set_min.
  case: arg_minP=> //.
  move=> x Hx /(_ y) Hy.
  by apply Hy.
  by apply ltnW.
Qed.

Lemma enumNext_cont (j : 'I_wordsize) (S: {set 'I_wordsize}) e (He: e \in S) f (Hf: set_isNext S f):
  set_min S e <= j -> j < set_next S f -> j \in S.
Proof.
  move=> Hj1 Hj2.
  case Hjmin: (set_min S e == j).
  + move: Hjmin=> /eqP Hjmin.
    rewrite -Hjmin.
    rewrite /set_min.
    case: arg_minP=> //.
  + have Hj1': set_min S e < j.
    rewrite ltn_neqAle.
    apply/andP; split=> //.
    apply negbT=> //.
    rewrite /set_min in Hj1.
    move: Hj1.
    case: arg_minP=> //.
    move=> i Hi1 Hi2 Hij.
    rewrite /set_next in Hj2.
    move: Hj2.
    case: arg_minP=> //.
    move=> k /andP [Hk1 Hk2] Hk3 Hjk.
    move: (Hk3 j)=> Hminj.
    rewrite leqNgt Hjk /= in Hminj.
    case HjS: (j \in S)=> //.
    apply Hminj.
    apply/andP; split.
    by rewrite HjS.
    apply/existsP.
    exists (set_min S e).
    apply/andP; split=> //.
    rewrite /set_min.
    case: arg_minP=> //.
Qed.

Lemma enumNext_correct (i: Int32) (S: {set 'I_wordsize}) e (H: e \in S) f (Hf: set_isNext S f):
  2 + set_min S e <= wordsize ->
  machine_repr i S -> machine_repr (enumNext i) (enumNext_set S e f).
Proof.
move=> Hlimit Hi.
apply union_repr=> //.
apply (min_ripple_repr _ _ _ H)=> //.
have ->: add (toInt 2) (ntz i) = toInt (2 + set_min S e).
  have ->: ntz i = toInt (set_min S e).
    move: (ntz_repr i e S Hi H)=> Hntz.
    rewrite /natural_repr in Hntz.
    move: Hntz=> /existsP [x /andP [Hx1 Hx2]].
    rewrite /native_repr in Hx1.
    move: Hx1=> /eqInt32P Hx1.
    rewrite Hx1.
    move: Hx2=> /eqP Hx2.
    rewrite -Hx2.
    by rewrite toInt_def.
  by rewrite ladd_repr.
have Hrepr: machine_repr (lxor i (add (keep_min i) i))
     (set_next S f |: [set x in S | x < set_next S f]).
  set E' := (set_next S f |: [set x0 in S | set_next S f < x0]).
  have ->: (set_next S f |: [set x0 in S | x0 < set_next S f]) = (S :\: E') :|: (E' :\: S).
    apply/setP=> x; rewrite !inE.
    rewrite negb_or negb_and.
    rewrite andb_orr.
    rewrite andb_orl.
    rewrite -andbA.
    rewrite andNb andbF.
    symmetry.
    rewrite -orbA orbC orbF.
    rewrite andb_orr.
    rewrite orbA.
    rewrite andbA.
    rewrite andNb orbF.
    rewrite -leqNgt.
    rewrite -ltn_neqAle.
    rewrite orbC.
    rewrite andb_idl.
    by rewrite andbC.
    move/eqP ->.
    rewrite /set_next.
    case: arg_minP=> //.
    move=> j Hj Hmin.
    by move: Hj=> /andP [Hj1 _].
  apply symdiff_repr=> //.
  by apply (min_ripple_repr _ _ _ H)=> //.
case: ifP=> Hnext'.
have ->: [set x0 in 'I_wordsize | x0 <= set_next S f - set_min S e - 2] =
[set i : 'I_wordsize | i < wordsize - (2 + set_min S e) & @inord wordsize.-1 (i + (2 + set_min S e)) \in ([set set_next S f] :|: [set x in S | x < set_next S f])].
  apply/setP=> x; rewrite !inE.
  rewrite andbC andbT.
  case Hx: (x < wordsize - (2 + set_min S e)).
  + have Hx': x < wordsize.
      apply (leq_trans (n := wordsize - (2 + set_min S e)))=> //.
      by apply leq_subr.
    rewrite [in _ || (_ && _)]andb_idl.
    rewrite -leq_eqVlt /=.
    have {2}->: set_next S f = inord (set_next S f - set_min S e - 2 + (2 + set_min S e)).
      apply ord_inj.
      rewrite inordK.
      rewrite -subnDA.
      rewrite [_ + 2]addnC.
      rewrite subnK //.
      rewrite addnC //.
      rewrite -subnDA.
      rewrite [_ + 2]addnC.
      rewrite subnK //.
      rewrite addnC //.
    rewrite !inordK.
    by rewrite leq_add2r.
    rewrite -subnDA.
    rewrite [set_min S e + 2]addnC.
    rewrite subnK=> //.
    by rewrite addnC.
    rewrite addnC -ltn_subRL=> //.
    move=> Hx''.
    apply (enumNext_cont _ _ e H f)=> //.
    rewrite inordK.
    rewrite addnA.
    by rewrite leq_addl.
    rewrite addnC -ltn_subRL=> //.
  + rewrite andbC andbF.
    rewrite leqNgt.
    apply negbF.
    rewrite ltnNge in Hx.
    have Hx': wordsize - (2 + set_min S e) <= x by apply negbFE; apply Hx.
    apply (leq_trans (n := wordsize - (2 + set_min S e)))=> //.
    rewrite -subnDA addnC.
    apply ltn_sub2r=> //.
    rewrite addnC.
    apply (leq_ltn_trans (n := set_next S f))=> //.
apply srn_repr=> //.
have ->: set0 = [set i : 'I_wordsize | i < wordsize - (2 + set_min S e) & @inord wordsize.-1 (i + (2 + set_min S e)) \in ([set set_next S f] :|: [set x in S | x < set_next S f])].
  apply/setP=> x; rewrite !inE.
  case Hx: (x < wordsize - (2 + set_min S e)); last by rewrite andbC andbF.
  rewrite andbC andbT.
  rewrite ltn_subRL addnC in Hx.
  case Hx': (inord (x + (2 + set_min S e)) == set_next S f).
  + exfalso.
    move: Hx'=> /eqP Hx'.
    have Hx'': x + (2 + set_min S e) = set_next S f.
      rewrite -Hx'.
      rewrite inordK=> //.
      rewrite -Hx'' in Hnext'.
      rewrite addnC in Hnext'.
      by rewrite leq_addl in Hnext'.
  + rewrite /=.
    have ->: (@inord wordsize.-1 (x + (2 + set_min S e)) < set_next S f) = false.
      rewrite inordK=> //.
      rewrite ltnNge.
      apply negbF.
      apply (leq_trans (n := set_min S e + 2)).
      apply ltnW.
      by rewrite ltnNge Hnext'.
      by rewrite addnC leq_addl.
    by rewrite andbF.
by apply srn_repr.
Qed.

Definition setToBs (E: {set 'I_wordsize}) : BITS wordsize := [tuple (i \in E) | i < wordsize].

Definition lt E1 E2 := toNat (setToBs E1) < toNat (setToBs E2).

Lemma reverse_orB (A: {set 'I_wordsize}) (B: {set 'I_wordsize}): setToBs (A :|: B) = orB (setToBs A) (setToBs B).
Admitted.

Definition disj (bs: BITS wordsize) (bs': BITS wordsize) := forall i, getBit bs i -> ~ (getBit bs' i) /\ getBit bs' i -> ~ (getBit bs i).

Lemma orB_disj (bs: BITS wordsize) bs' : disj bs bs' -> toNat (orB bs bs') = (toNat bs) + (toNat bs').
Admitted.

Lemma enumNext_sameCard (S: {set 'I_wordsize}) e (H: e \in S) f (Hf: set_isNext S f):
  #|enumNext_set S e f| = #|S|.
Admitted.

Lemma enumNext_inc (S: {set 'I_wordsize}) e (H: e \in S) f (Hf: set_isNext S f):
  lt S (enumNext_set S e f).
Proof.
  rewrite /enumNext_set.
  have Hdec: S = [set x in S | set_next S f < x] :|: [set x in S | set_next S f > x].
    apply/setP=> x; rewrite !inE.
    rewrite -andb_orr.
    case Hx: (x \in S)=> //=.
    rewrite -neq_ltn.
    apply/eqP.
    rewrite eq_sym.
    rewrite eqb_id.
    apply/eqP=> Habs.
    have Habs': x = set_next S f.
      by apply ord_inj.
    rewrite Habs' in Hx.
    move: Hx.
    rewrite /set_next.
    case: arg_minP=> //.
    move=> y /andP [Habs1 _] Hmin Habs2.
    by rewrite Habs2 in Habs1.
  have Hlt: toNat (setToBs [set x in S | x < set_next S f]) < toNat (setToBs [set set_next S f]).
    by admit.
  have Hdisj1: disj (setToBs [set set_next S f]) (setToBs [set x in S | set_next S f < x]).
    by admit.
  have Hdisj2: disj (orB (setToBs [set set_next S f]) (setToBs [set x in S | set_next S f < x]))
                    (setToBs [set x in 'I_wordsize | x <= set_next S f - set_min S e - 2]).
    by admit.
  have Hdisj3: disj (setToBs [set x in S | set_next S f < x])
                    (setToBs [set x in S | x < set_next S f]).
    by admit.
  case Hlimit: (set_min S e + 2 <= set_next S f).
  rewrite /lt.
  rewrite /enumNext_set.
  rewrite {1}Hdec.
  rewrite !reverse_orB.
  rewrite !orB_disj=> //.
  rewrite [toNat (setToBs [set set_next S f]) + toNat (setToBs [set x in S | set_next S f < x])]addnC.
  rewrite -addnA.
  rewrite ltn_add2l.
  apply (leq_trans (n := toNat (setToBs [set set_next S f])))=> //.
  apply leq_addr.
  (****)
  rewrite setU0.
  rewrite {1}Hdec.
  rewrite /lt /enumNext_set.
  rewrite !reverse_orB.
  rewrite !orB_disj=> //.
  rewrite addnC ltn_add2r=> //.
Admitted.

Lemma enumNext_isSucc (S: {set 'I_wordsize}) e (H: e \in S) f (Hf: set_isNext S f):
  forall y, y <> enumNext_set S e f -> #|y| = #|S| -> lt S y -> lt (enumNext_set S e f) y.
Proof.
  case Hlimit: (set_min S e + 2 <= set_next S f).
  move=> y Hy1 Hy2 Hy3.
  (* If y contains bigger than [set s_next f] :|: [set x in S | x > s_next f], then ok *)
  (* Otherwise, it must be bigger than enumNext_set because it is bigger than the set {0, 1, ...} *)
  admit.
  (****)
  move=> y Hy1 Hy2 Hy3.
  (* This case corresponds to set_next S f = set_min S e + 1 *)
  admit.
Admitted.

Definition allEnums_set n k e f := mkseq (fun n => iter n (fun x => enumNext_set x e f) [set x : 'I_wordsize | x < k]) 'C(n, k).

Definition allEnums n k := mkseq (fun n => iter n enumNext (dec (lsl one (toInt k)))) 'C(n, k).

Definition allSubsets n k := [set A : {set 'I_wordsize} | (#|A| == k) && [forall x, (x \in A) ==> (x < n)]].

Lemma enumsNext_allEnum_set: forall n k e f x, x \in (allEnums_set n k e f) <-> x \in (allSubsets n k).
Proof.
  move=> n k e f x.
  split.
  rewrite /allEnums_set /mkseq.
  move: ('C(n, k)) x; elim=> //.
  move=> n0 Hn0 x Hx.
  rewrite /= in Hx.
  rewrite !inE in Hx.
  move: Hx=> /orP; elim=> Hx.
  rewrite /allSubsets !inE.
  apply/andP; split.
  admit. (* size_full in queens *)
  apply/forallP=> y.
  apply/implyP=> Hy.
  move: Hx=> /eqP Hx.
  rewrite Hx !inE in Hy.
  admit. (* TODO: add k <= n to the list of hypotheses *)
  move: Hx=> /mapP [x0 Hx0 Hx0'].
  rewrite mem_iota in Hx0.
  move: Hx0=> /andP [Hx01 Hx02].
  have Hx01': x0 = x0.-1.+1 by rewrite prednK.
  rewrite Hx01' /= in Hx0'.
  rewrite Hx0'.
  rewrite /allSubsets !inE.
  apply/andP; split.
  rewrite enumNext_sameCard.
  have Hn0': forall x, x \in [seq iter n (fun x0 : {set 'I_wordsize} => enumNext_set x0 e f)
                     [set x0 : 'I_wordsize | x0 < k]| n <- iota 0 n0] -> #|x| = k.
    by admit.
  move: (Hn0' (iter x0.-1 (fun x1 : {set 'I_wordsize} => enumNext_set x1 e f)
       [set x1 : 'I_wordsize | x1 < k]))=> Hn0''.
  apply/eqP/Hn0''.
  apply/mapP; exists x0.-1=> //.
  rewrite mem_iota.
  apply/andP; split=> //.
  rewrite add0n.
  rewrite -(ltn_add2l 1).
  rewrite addnC addn1 prednK=> //.
  (* e and f... *)
  admit.
  admit.
  admit. (* Hm... *)
  (********************************)
  move=> H.
  admit. (* Now that's the tricky part *)
Admitted.

Fail Theorem enumsNext_allEnum: forall n k x, x \in (allEnums n k) <-> exists y, y \in (allSubsets n k) /\ machine_repr x y.

Cd "examples/enum_parts".

Require Import ExtrOcamlBasic.

Extraction "enum_parts.ml" enumNext.

Cd "../..".
