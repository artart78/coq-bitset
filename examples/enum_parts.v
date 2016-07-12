Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset binomial bigop.
From Bits
     Require Import bits extraction.axioms32.

Require Import repr_op.

Definition enumNext (x: Int32) := (* 111001100 *)
  let smallest := keep_min x in(* 000000100 *)
  let ripple := add smallest x in  (* 111010000 *)
  let ones := lsr (lxor x ripple) (add (toInt 2) (ntz x)) in
  lor ripple ones.

Definition set_isNext (S: {set 'I_wordsize}) x := (x \notin S) && [exists y, (y \in S) && (y < x)].

Definition set_next (S: {set 'I_wordsize}) := [arg min_(x < ord0 | set_isNext S x) x].

Definition set_min (S: {set 'I_wordsize}) := [arg min_(x < ord0 in S) x].

Definition enumNext_set (S: {set 'I_wordsize}) :=
  let s_min := set_min S in
  let s_next := set_next S in
  [set s_next] :|: [set x in S | x > s_next] :|: (if s_next >= s_min + 2 then [set x in 'I_wordsize | x <= (s_next - s_min - 2)] else set0).

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

Definition set_next_g {n} (S: {set 'I_n.+1}) x := [arg min_(y < ord0 | set_isNext_g S y x) y].

Lemma pick_exists n (P: 'I_n -> bool) e (He: P e):
  ([pred i | P i & [forall (j | P j), i <= j]] =1 xpred0) -> False.
Admitted.

Lemma ripple_repr_1':
  forall n (bs: BITS n.+1) E f, spec.repr bs E -> set_isNext_g E f (@ord0 n) ->
    spec.repr (addB [tuple of true :: spec.zero n] bs) ((set_next_g E (@ord0 n)) |: [set y in E | y > set_next_g E (@ord0 n)]).
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
      have ->: (ord0 == set_next_g E 0) = false.
        apply/eqP=> Habs.
        rewrite /set_next_g in Habs.
        move: Habs.
        case: arg_minP=> //.
        rewrite -Hf //.
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
      have ->: ord0 == set_next_g E 0.
        rewrite /set_next_g.
        case: arg_minP=> //.
        rewrite -Hf //.
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
        rewrite /arg_min.
        case: pickP=> //=.
        move=> i0 /andP[Hi0 /forallP Hi0'] Habs.
        rewrite -Habs in Hi0.
        move: Hi0=> /andP[Habs' _].
        by rewrite Hbs' in Habs'.
        move=> Habs.
        exfalso.
        apply (pick_exists n.+2 (fun i => set_isNext_g E i 0) f)=> //.
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
        have Hnext: set_next_g E 0 = inord (set_next_g E' 0).+1.
          rewrite /set_next_g.
          case: arg_minP=> //.
          admit.
          move=> i0 Hi0 Hi0'.
          case: arg_minP=> //.
          admit.
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
        have ->: (inord i.-1.+1 == set_next_g E 0) = (inord i.-1 == set_next_g E' 0).
          rewrite Hnext.
          apply/eqP.
          case H: (inord i.-1 == set_next_g E' 0).
          + move/eqP: H=> H.
            apply ord_inj.
            rewrite !inordK=> //.
            apply/eqP.
            rewrite eqSS.
            rewrite -H.
            rewrite inordK=> //.
            apply (leq_trans (n := i))=> //.
            rewrite -ltnS=> //.
            rewrite -[(set_next_g E' 0).+1]addn1 -[n.+2]addn1.
            by rewrite ltn_add2r.
            rewrite prednK=> //.
          + move/eqP: H=> H.
            move=> Habs.
            have Habs': inord i.-1 = set_next_g E' 0.
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
              by rewrite -[(set_next_g E' 0).+1]addn1 -[n.+2]addn1 ltn_add2r.
              apply (leq_trans (n := i))=> //.
              rewrite -ltnS=> //.
            by rewrite Habs' in H.
        have ->: (set_next_g E 0 < @inord n.+1 i.-1.+1) = (set_next_g E' 0 < i.-1).
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
      have ->: set_next_g E (@ord0 n.+1) = @ord0 n.+1.
        rewrite /set_next_g.
        case: arg_minP=> //.
        admit.
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
Admitted.

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
    spec.repr (addB bs' bs) ((set_next_g E x) |: [set y in E | y < x] :|: [set y in E | y > set_next_g E x]).
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
    rewrite [(i \in E) && (set_next_g E x < i)]andbC.
    rewrite -orbA.
    rewrite andKb.
    have ->: (i == set_next_g E x) = false.
      apply/eqP=> Habs.
      have Habs': set_next_g E x >= x.
        rewrite /set_next_g.
        case: arg_minP=> //.
        admit.
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
    have Hf'2: set_next_g E' 0 = inord ((set_next_g E x) - x).
      rewrite /set_next_g.
      apply ord_inj.
      rewrite inordK.
      case: arg_minP=> //.
      admit.
      move=> i0 /andP [Hi0 _] Hi0'.
      case: arg_minP=> //.
      admit.
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
      rewrite (Hlt [arg min_(y < ord0 | set_isNext_g E y x) y])=> //.
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
    have ->: (@inord (n - x) (i - x) == inord (set_next_g E x - x)) = (i == set_next_g E x).
      apply/eqP.
      case Hi': (i == set_next_g E x).
      + move: Hi'=> /eqP Hi'.
        by rewrite Hi'.
      + move: Hi'=> /eqP Hi'.
        move=> Habs.
        have Habs': i = set_next_g E x.
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
        admit.
        by move=> i0 /andP[_ Habs'] _.
        rewrite (Hlt (set_next_g E x))=> //.
      by rewrite Habs' in Hi'.
    have ->: (@inord n (@inord (n - x) (i - x) + x) \in E) = (i \in E).
      rewrite inordK.
      rewrite subnK.
      by rewrite inord_val.
      by rewrite leqNgt Hi.
      by rewrite (Hlt i).
    rewrite !inordK.
    have ->: (set_next_g E x - x < i - x) = (set_next_g E x < i).
      case Hi': (set_next_g E x < i).
      + rewrite ltn_sub2r=> //.
        move: Hi'.
        rewrite /set_next_g.
        case: arg_minP=> //.
        admit.
        move=> i0 /andP[_ Hi0] Hmin Hi0'.
        apply (leq_ltn_trans (n := i0))=> //.
      + apply/negP=> Habs.
        have Habs': set_next_g E x < i.
          have ->: nat_of_ord (set_next_g E x) = set_next_g E x - x + x.
            rewrite subnK=> //.
            rewrite /set_next_g.
            case: arg_minP=> //.
            admit.
            by move=> i0 /andP[_ Hi0] _.
          have ->: nat_of_ord i = i - x + x.
            rewrite subnK=> //.
            by rewrite leqNgt Hi.
          by rewrite ltn_add2r Habs.
        by rewrite Habs' in Hi'.
    rewrite //.
    rewrite (Hlt i)=> //.
    rewrite (Hlt (set_next_g E x))=> //.
Admitted.

Lemma ripple_repr:
  forall i j S x f, machine_repr i S -> machine_repr j [set x] -> set_isNext_g S f x ->
    machine_repr (add j i) ((set_next_g S x) |: [set y in S | y < x] :|: [set y in S | y > set_next_g S x]).
Proof.
  move=> i j S x f [bv [r_native r_set]] [bv' [r_native' r_set']] Hx.
  exists (addB bv' bv); split.
  apply add_repr=> //.
  by apply (ripple_repr_1 _ _ _ _ _ f).
Qed.

(* TODO: move from queens to somewhere else *)
Lemma ladd_repr:
  forall x y, add (toInt x) (toInt y) = toInt (x + y).
Admitted.

Lemma min_ripple_repr i (S: {set 'I_wordsize}) e (He: e \in S) f (Hf: set_isNext S f):
  machine_repr i S ->
  machine_repr (add (keep_min i) i) (set_next S |: [set x in S | set_next S < x]).
Proof.
  have HS: set_next S = set_next_g S (set_min S).
    rewrite /set_next /set_next_g.
    rewrite /arg_min.
    rewrite (eq_pick (Q := [pred i0 | set_isNext_g S i0 (set_min S) & [
               forall (j | set_isNext_g S j (set_min S)),
                 i0 <= j]])) //.
    move=> x /=.
    have Heq: forall x, [exists y, (y \in S) && (y < x)] = (set_min S < x).
      move=> x0.
      rewrite /set_min.
      case: arg_minP.
      admit.
      move=> j Hj Hj'.
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
    have Hhandy: forall y, (y \notin S) && (set_min S < y) = (y \notin S) && (set_min S <= y).
      move=> y.
      apply andb_id2l=> Hy.
      rewrite [set_min S <= y]leq_eqVlt.
      have Habs: set_min S \in S.
        rewrite /set_min.
        case: arg_minP=> //.
        admit.
      have ->: (nat_of_ord (set_min S) == nat_of_ord y) = false.
        apply negbTE.
        apply/eqP=> Habs'.
        have Habs'': set_min S = y by apply ord_inj.
        rewrite Habs'' in Habs.
        by rewrite Habs in Hy.
      by rewrite /=.
    have ->: [forall (j | (j \notin S) && [exists y, (y \in S) && (y < j)]), x <= j]
           = [forall (j | (j \notin S) && (set_min S <= j)), x <= j].
      apply eq_forallb=> y.
      rewrite Heq.
      by rewrite Hhandy.
    rewrite /set_isNext_g.
    rewrite Hhandy.
    rewrite //.
  have ->: (set_next S |: [set x0 in S | set_next S < x0]) = ((set_next_g S (set_min S)) |: [set y in S | y < (set_min S)] :|: [set y in S | y > set_next_g S (set_min S)]).
    have ->: [set y in S | y < set_min S] = set0.
      apply/setP=> x; rewrite !inE.
      rewrite /set_min.
      case: arg_minP=> //.
      admit.
      move=> j Hj /(_ x) Hj'.
      case Hx: (x \in S); rewrite andbC.
      rewrite andbT.
      apply negbTE.
      rewrite -leqNgt.
      by apply Hj'.
      by rewrite andbF.
    by rewrite setU0 HS.
  move=> H.
  eapply ripple_repr=> //.
  admit.
  have Hf': set_isNext_g S f (set_min S).
  rewrite /set_isNext_g.
  move: Hf=> /andP [Hf1 /existsP [y /andP [Hy1 Hy2]]].
  apply/andP; split=> //.
  apply (leq_trans (n := y))=> //.
  rewrite /set_min.
  case: arg_minP=> //.
  admit.
  move=> x Hx /(_ y) Hy.
  by apply Hy.
  by apply ltnW.
  apply Hf'.
Admitted.

Lemma enumNext_cont (j : 'I_wordsize) (S: {set 'I_wordsize}) e (He: e \in S) f (Hf: set_isNext S f):
  set_min S <= j -> j < set_next S -> j \in S.
Proof.
  move=> Hj1 Hj2.
  case Hjmin: (set_min S == j).
  + move: Hjmin=> /eqP Hjmin.
    rewrite -Hjmin.
    rewrite /set_min.
    case: arg_minP=> //.
    admit.
  + have Hj1': set_min S < j.
    rewrite ltn_neqAle.
    apply/andP; split=> //.
    apply negbT=> //.
    rewrite /set_min in Hj1.
    move: Hj1.
    case: arg_minP=> //.
    admit.
    move=> i Hi1 Hi2 Hij.
    rewrite /set_next in Hj2.
    move: Hj2.
    case: arg_minP=> //.
    admit.
    move=> k /andP [Hk1 Hk2] Hk3 Hjk.
    move: (Hk3 j)=> Hminj.
    rewrite leqNgt Hjk /= in Hminj.
    case HjS: (j \in S)=> //.
    apply Hminj.
    apply/andP; split.
    by rewrite HjS.
    apply/existsP.
    exists (set_min S).
    apply/andP; split=> //.
    rewrite /set_min.
    case: arg_minP=> //.
    admit.
Admitted.

Lemma ntz_repr:
  forall (bs: Int32) x y E, machine_repr bs E -> x \in E ->
    natural_repr (ntz bs) [arg min_(k < y in E) k].
Admitted.

Lemma enumNext_correct (i: Int32) (S: {set 'I_wordsize}) e (H: e \in S) f (Hf: set_isNext S f):
  2 + set_min S <= wordsize ->
  machine_repr i S -> machine_repr (enumNext i) (enumNext_set S).
Proof.
move=> Hlimit Hi.
apply union_repr=> //.
apply (min_ripple_repr _ _ _ H _ Hf)=> //.
have ->: add (toInt 2) (ntz i) = toInt (2 + set_min S).
  have ->: ntz i = toInt (set_min S).
    move: (ntz_repr i e ord0 S Hi H)=> Hntz.
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
     (set_next S |: [set x in S | x < set_next S]).
  set E' := (set_next S |: [set x0 in S | set_next S < x0]).
  have ->: (set_next S |: [set x0 in S | x0 < set_next S]) = (S :\: E') :|: (E' :\: S).
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
    admit.
    move=> j Hj Hmin.
    by move: Hj=> /andP [Hj1 _].
  apply symdiff_repr=> //.
  by apply (min_ripple_repr _ _ _ H _ Hf)=> //.
case: ifP=> Hnext'.
have ->: [set x0 in 'I_wordsize | x0 <= set_next S - set_min S - 2] =
[set i : 'I_wordsize | i < wordsize - (2 + set_min S) & @inord wordsize.-1 (i + (2 + set_min S)) \in ([set set_next S] :|: [set x in S | x < set_next S])].
  apply/setP=> x; rewrite !inE.
  rewrite andbC andbT.
  case Hx: (x < wordsize - (2 + set_min S)).
  + have Hx': x < wordsize.
      apply (leq_trans (n := wordsize - (2 + set_min S)))=> //.
      by apply leq_subr.
    rewrite [in _ || (_ && _)]andb_idl.
    rewrite -leq_eqVlt /=.
    have {2}->: set_next S = inord (set_next S - set_min S - 2 + (2 + set_min S)).
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
    rewrite [set_min S + 2]addnC.
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
    have Hx': wordsize - (2 + set_min S) <= x by apply negbFE; apply Hx.
    apply (leq_trans (n := wordsize - (2 + set_min S)))=> //.
    rewrite -subnDA addnC.
    apply ltn_sub2r=> //.
    rewrite addnC.
    apply (leq_ltn_trans (n := set_next S))=> //.
apply srn_repr=> //.
have ->: set0 = [set i : 'I_wordsize | i < wordsize - (2 + set_min S) & @inord wordsize.-1 (i + (2 + set_min S)) \in ([set set_next S] :|: [set x in S | x < set_next S])].
  apply/setP=> x; rewrite !inE.
  case Hx: (x < wordsize - (2 + set_min S)); last by rewrite andbC andbF.
  rewrite andbC andbT.
  rewrite ltn_subRL addnC in Hx.
  case Hx': (inord (x + (2 + set_min S)) == set_next S).
  + exfalso.
    move: Hx'=> /eqP Hx'.
    have Hx'': x + (2 + set_min S) = set_next S.
      rewrite -Hx'.
      rewrite inordK=> //.
      rewrite -Hx'' in Hnext'.
      rewrite addnC in Hnext'.
      by rewrite leq_addl in Hnext'.
  + rewrite /=.
    have ->: (@inord wordsize.-1 (x + (2 + set_min S)) < set_next S) = false.
      rewrite inordK=> //.
      rewrite ltnNge.
      apply negbF.
      apply (leq_trans (n := set_min S + 2)).
      apply ltnW.
      by rewrite ltnNge Hnext'.
      by rewrite addnC leq_addl.
    by rewrite andbF.
by apply srn_repr.
Admitted.

Lemma enumNext_sameCard (S: {set 'I_wordsize}) e (H: e \in S) f (Hf: set_isNext S f):
  #|enumNext_set S| = #|S|.
Proof.
rewrite /enumNext_set.
have H1: set_next S \notin [set x in S | set_next S < x].
  apply/negP=> Habs.
  by rewrite !inE ltnn andbF in Habs.
have HS: forall x, x \in S -> set_min S <= x.
  move=> x Hx.
  rewrite /set_min.
  case: arg_minP=> //.
  admit.
  by move=> i Hi /(_ x Hx) ->.
have H2: set_min S < set_next S.
  rewrite /set_next.
  case: arg_minP=> //.
  admit.
  move=> i /andP [_ /existsP [x /andP [Hx1 Hx2]]] _.
  apply (leq_ltn_trans (n := x))=> //.
  by apply (HS x Hx1).
have H3: set_min S \notin [set x in S | set_next S < x].
  apply/negP=> Habs.
  rewrite !inE in Habs.
  move: Habs=> /andP [_ Habs].
  rewrite ltnNge in Habs.
  move: Habs=> /negP Habs.
  apply Habs.
  by rewrite ltnW.
have H4: (set_next S |: [set x in S | set_next S < x]) :&: [set x : 'I_wordsize | x <= set_next S - set_min S - 2] = set0.
  apply/setP=> x; rewrite !inE.
  apply/negP=> /andP [/orP Habs1 Habs2].
  have Habs': x >= set_next S.
    case: Habs1=> Habs1.
    move: Habs1=> /eqP Habs1.
    rewrite Habs1=> //.
    move: Habs1=> /andP [_ Habs1].
    by apply ltnW.
  have Habs'': false.
    rewrite -(ltnn (set_next S)).
    apply (leq_ltn_trans (n := (set_next S - set_min S - 2))).
    apply (leq_trans (n := x))=> //.
    rewrite -subnDA.
    rewrite -{2}[nat_of_ord (set_next S)]subn0.
    apply ltn_sub2l.
    apply (leq_ltn_trans (n := set_min S))=> //.
    have {2}->: 2 = 1 + 1 by trivial.
    by rewrite addnA addn1.
  by trivial.
have H5: (set_min S |: [set x in S | set_next S < x]) :&: [set x in S | x < set_next S & set_min S < x] = set0.
  apply/setP=> x; rewrite !inE.
  apply/negP=> /andP [/orP Habs1 /andP [Habs2 /andP [Habs3 Habs4]]].
  case: Habs1=> Habs1.
  move: Habs1=> /eqP Habs1.
  rewrite Habs1 in Habs4.
  have Habs': false by rewrite -(ltnn (set_min S)).
  rewrite //.
  move: Habs1=> /andP [_ Habs1].
  have Habs': false.
    rewrite -(ltnn (set_next S)).
    by apply (ltn_trans (n := x)).
  rewrite //.
have HSmin: set_min S \in S.
  rewrite /set_min.
  case: arg_minP=> //.
  admit.
rewrite cardsU cardsU1 H1 /=.
case Hc: (set_min S + 2 <= set_next S).
+ rewrite H4 cards0 subn0.
  have {5}->: S = (set_min S) |: [set x in S | set_next S < x] :|: [set x in S | (set_next S > x) && (x > set_min S)].
    by admit.
  rewrite cardsU.
  rewrite H5.
  rewrite cards0 subn0.
  rewrite cardsU1 H3 /=.
  have ->: [set x in S | x < set_next S & set_min S < x] = [set x : 'I_wordsize | x < set_next S & set_min S < x].
    apply/setP=> x; rewrite !inE.
    rewrite andb_idl=> //.
    move=> /andP [Hx1 Hx2].
    move: Hx1.
    rewrite /set_next.
    case: arg_minP=> //.
    admit.
    move=> i Hi Hmin Hi'.
    rewrite ltnNge in Hi'.
    apply/negP=> /negP Habs.
    have Habs': i <= x.
      apply Hmin.
      apply/andP; split=> //.
      apply/existsP.
      exists (set_min S).
      by rewrite HSmin Hx2.
    by rewrite Habs' in Hi'.
  have ->: #|[set x : 'I_wordsize | x <= set_next S - set_min S - 2]| = set_next S - set_min S - 1 by admit.
  have ->: #|[set x : 'I_wordsize | x < set_next S & set_min S < x]| = set_next S - set_min S - 1 by admit.
  by trivial.
+ rewrite setI0 cards0 addn0 subn0.
  have Hc': set_next S < set_min S + 2.
    by rewrite ltnNge Hc.
  have Hc'': nat_of_ord (set_next S) = set_min S + 1.
    apply/eqP.
    rewrite eqn_leq.
    apply/andP; split.
    + rewrite -(leq_add2r 1).
      rewrite -addnA /=.
      rewrite -addn1 in Hc'.
      by apply Hc'.
    + rewrite addn1.
      rewrite ltn_neqAle.
      apply/andP; split.
      - apply/eqP=> Habs.
        move: (ord_inj Habs)=> Habs'.
        have Habs'': set_next S \in S.
          rewrite -Habs'.
          rewrite /set_min.
          case: arg_minP=> //.
          admit.
        move: Habs''.
        rewrite /set_next.
        case: arg_minP=> //.
        admit.
        move=> i /andP[Hi1 _] _ Hi2.
        by rewrite Hi2 in Hi1.
      - rewrite /set_next.
        case: arg_minP=> //.
        admit.
        move=> i /andP [_ /existsP [x /andP [Hx1 Hx2]]] _.
        apply (leq_trans (n := x)).
        apply HS=> //.
        apply ltnW=> //.
  have {3}->: S = (set_min S) |: [set x in S | set_next S < x].
    apply/setP=> x; rewrite !inE.
    case Hx: (x \in S)=> //.
    - rewrite /=.
      case Hx2: (x <= set_min S).
      + rewrite leq_eqVlt in Hx2.
        move: Hx2=> /orP; elim=> Hx2.
        move: Hx2=> /eqP Hx2.
        move: (ord_inj Hx2)=> Hx3.
        by rewrite Hx3 eq_refl.
        exfalso.
        move: Hx2; rewrite /set_min.
        case: arg_minP=> //.
        admit.
        move=> i Hi /(_ x) Hmin.
        by rewrite ltnNge Hmin.
      + have ->: set_next S < x.
          rewrite ltn_neqAle.
          apply/andP; split.
          apply/negP=> /eqP Habs.
          have Habs': x = inord (set_next S).
            rewrite Habs.
            apply ord_inj.
            by rewrite inordK=> //.
          rewrite Habs' in Hx.
          move: Hx.
          rewrite /set_next.
          case: arg_minP=> //.
          admit.
          move=> i /andP [Hi _] Hmin Hi'.
          rewrite inord_val in Hi'.
          by rewrite Hi' in Hi.
          rewrite Hc''.
          by rewrite addn1 ltnNge Hx2.
        by rewrite orbT.
    - rewrite orbF.
      symmetry.
      apply negbTE.
      apply/negP=> /eqP Habs.
      rewrite Habs in Hx.
      by rewrite HSmin in Hx.
  by rewrite cardsU1 H3.
Admitted.

Definition indToSet k n := iter n (fun x => enumNext_set x) [set x : 'I_wordsize | x < k].

Definition setToInd k (S: {set 'I_wordsize}) := \sum_(i in 'I_k) 'C(nth ord0 (enum S) i, i.+1).

Lemma setToInd_next k S: setToInd k (enumNext_set S) = (setToInd k S).+1.
Proof.
(* Induction in Knuth's formula... *)
Admitted.

Lemma indToSet_inv k: cancel (indToSet k) (setToInd k).
Proof.
elim=> [|n IHn].
+ (* n = 0 *)
  rewrite /setToInd /=.
  apply/eqP.
  rewrite sum_nat_eq0.
  apply/forallP=> x.
  apply/implyP=> Hx.
  rewrite bin_small //.
  admit. (* Seems trivial *)
+ (* n ~ n.+1 *)
  by rewrite setToInd_next IHn.
Admitted.

Lemma setToInd_inj k: injective (setToInd k).
Admitted.

Lemma setToInd_inv k: cancel (setToInd k) (indToSet k).
Proof.
apply inj_can_sym.
apply indToSet_inv.
apply setToInd_inj.
Qed.

Canonical int_eqMixin := EqMixin eqInt32P.
Canonical int_eqType := Eval hnf in EqType Int32 int_eqMixin.

Definition allEnums_set n k := [set (indToSet k (nat_of_ord y)) | y in 'I_('C(n, k))].

Lemma allEnums_sameCard: forall n k, #|indToSet k n| = k.
Proof.
move=> n k.
elim: n=> [|n IHn].
rewrite /=.
admit. (* Proof already in n-queens *)
rewrite /=.
rewrite (enumNext_sameCard _ ord0 _ ord0)=> //.
admit. (* e *)
admit. (* f *)
Admitted.

Definition indToInt k n := iter n enumNext (dec (lsl one (toInt k))).

Definition allEnums n k := mkseq (indToInt k) 'C(n, k).

Definition allSubsets n k := [set A : {set 'I_wordsize} | (#|A| == k) && [forall x, (x \in A) ==> (x < n)]].

Lemma setToInd_bounded x n k: x \in allSubsets n k -> setToInd k x < 'C(n, k).
Admitted.

Lemma indToSet_bounded S n k x: setToInd k S < 'C(n, k) -> x \in S -> x < n.
Admitted.

Lemma allEnums_eq: forall n k, k <= n -> allEnums_set n k = allSubsets n k.
Proof.
move=> n k Hk.
apply/eqP.
rewrite eqEsubset.
apply/andP; split.
+ (* allEnums_set \subset allSubsets *)
  apply/subsetP=> x Hx.
  rewrite /allSubsets !inE.
  move: Hx=> /imsetP [y Hy1 Hy2].
  apply/andP; split.
  rewrite Hy2 allEnums_sameCard=> //.
  apply/forallP=> x0.
  apply/implyP=> Hx0.
  apply (indToSet_bounded x _ k)=> //.
  rewrite Hy2 indToSet_inv=> //.
+ (* allSubsets \subset allEnums_set *)
  apply/subsetP=> x Hx.
  apply/imsetP.
  have Hcast: 'C(n, k).-1.+1 = 'C(n, k).
    rewrite prednK=> //.
    by rewrite bin_gt0.
  exists (cast_ord Hcast (inord (setToInd k x)))=> //.
  rewrite /= inordK.
  by rewrite setToInd_inv.
  rewrite Hcast.
  by apply setToInd_bounded.
Qed.

Lemma allEnums_repr_i: forall k i,
  machine_repr (indToInt k i) (indToSet k i).
Proof.
  move=> k.
  elim=> [|n IHn].
  rewrite /=.
  admit. (* Similar to 'create' *)
  rewrite /=.
  eapply (enumNext_correct _ _ ord0 _ ord0)=> //.
  admit. (* e *)
  admit. (* f *)
Admitted.

(* TODO: move somewhere else *)
Lemma machine_repr_inj1: forall x y z, machine_repr x y -> machine_repr z y -> x = z.
Proof.
  move=> x y z [bx [/eqP-> Hx]] [bz [/eqP-> Hz]].
  have ->: bx = bz=> //.
  apply allBitsEq=> i Hi.
  have ->: getBit bx i = (inord i \in y) by rewrite Hx inE inordK.
  by have ->: getBit bz i = (inord i \in y) by rewrite Hz inE inordK.
Qed.

Lemma allEnums_repr: forall n k x, k <= n ->
  x \in (allEnums n k) <-> exists y, y \in (allEnums_set n k) /\ machine_repr x y.
Proof.
move=> n k x Hk.
split.
+ (* -> *)
  move=> Hx.
  rewrite /allEnums in Hx.
  move: Hx=> /mapP [i Hi Hx].
  exists (indToSet k i); split.
  rewrite /allEnums_set.
  apply/imsetP.
  have Hcast: 'C(n, k).-1.+1 = 'C(n, k).
    rewrite prednK=> //.
    by rewrite bin_gt0.
  exists (cast_ord Hcast (@inord 'C(n, k).-1 i))=> //.
  rewrite /= inordK=> //.
  rewrite Hcast.
  move: (mem_iota 0 'C(n, k) i)=> Hi'.
  rewrite Hi in Hi'.
  by rewrite /= add0n in Hi'.
  rewrite Hx.
  by apply allEnums_repr_i.
+ (* <- *)
  move=> [y [Hy1 Hy2]].
  rewrite /allEnums.
  rewrite /allEnums_set in Hy1.
  apply/mapP.
  move: Hy1=> /imsetP [z Hz1 Hz2].
  exists (nat_of_ord z).
  rewrite mem_iota /= add0n //.
  apply (machine_repr_inj1 _ y)=> //.
  rewrite Hz2.
  by apply allEnums_repr_i.
Qed.

Theorem enumsNext_allEnum: forall n k x, k <= n < wordsize -> x \in (allEnums n k) <-> exists y, y \in (allSubsets n k) /\ machine_repr x y.
Proof.
move=> n k x Hn.
move: Hn=> /andP [Hk Hn].
move: (allEnums_repr n k x Hk)=> H.
by rewrite -allEnums_eq.
Qed.

Cd "examples/enum_parts".

Require Import ExtrOcamlBasic.

Extraction "enum_parts.ml" enumNext.

Cd "../..".
