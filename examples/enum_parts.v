Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
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

Definition set_isNext_g {n} (S: {set 'I_n.+1}) y x := (y \notin S) && (y > x).

Definition set_next_g {n} (S: {set 'I_n.+1}) f x := [arg min_(y < f | set_isNext_g S y x) y].

Lemma ripple_repr_1:
  forall n (bs: BITS n.+1) bs' E x f, spec.repr bs E -> spec.repr bs' [set x] -> x \in E -> set_isNext_g E f x ->
    spec.repr (addB bs' bs) ((set_next_g E f x) |: [set y in E | y < x] :|: [set y in E | y > set_next_g E f x]).
Proof.
  elim=> [|n HI] /tupleP[b bs] /tupleP[b' bs'] E x f Hbs Hbs' Hx1 Hx2.
  + (* n.+1 = 1 *)
    exfalso.
    have Hx': x = ord0.
      elim x; elim=> [i|i Hi] //; by apply ord_inj.
    have Hf: f = ord0.
      elim f; elim=> [i|i Hi] //; by apply ord_inj.
    by rewrite Hx' Hf /set_isNext_g ltn0 andbF in Hx2.
  + (* n.+1 ~ n.+2 *)
    case: b' Hbs'=> Hbs'.
    + (* b' = true, ie x = 0 *)
      have Hx: x = ord0.
        rewrite /spec.repr in Hbs'.
        move: Hbs'=> /setP /(_ ord0) Hbs'.
        rewrite !inE /getBit /= in Hbs'.
        by apply/eqP; rewrite eq_sym Hbs'.
      rewrite Hx in Hx1 Hx2 Hbs'.
      rewrite Hx.
      have Hb: b = true.
        move: Hbs=> /setP /(_ ord0) Hbs.
        by rewrite Hx1 inE /getBit /= in Hbs.
      rewrite Hb.
      have ->: bs' = spec.zero n.+1.
        apply allBitsEq=> i Hi.        
        rewrite /spec.repr in Hbs'.
        move: Hbs'=> /setP Hbs'.
        have ->: getBit bs' i = getBit [tuple of true :: bs'] i.+1 by trivial.
        rewrite -fromNat0 getBit_zero.
        move: (Hbs' (inord i.+1))=> Hbs'1.
        rewrite !inE inordK in Hbs'1.
        rewrite -Hbs'1.
        apply/eqP=> H.
        have: nat_of_ord (@inord n.+1 i.+1) = nat_of_ord (@ord0 n.+1) by rewrite H.
        rewrite inordK=> //.
        by rewrite -[i.+1]addn1 -[n.+2]addn1 ltn_add2r.
      have ->: addB [tuple of true :: spec.zero n.+1] [tuple of true :: bs] = [tuple of false :: (addB [tuple of true :: spec.zero n] bs)].
        apply allBitsEq.
        elim=> [Hi|i HIi Hi].
        rewrite {2}/getBit /adcB /=.
        rewrite !tuple.beheadCons !tuple.theadCons /=.
        by admit.
        have ->: getBit [tuple of false :: addB [tuple of true :: spec.zero n] bs] i.+1 = getBit (addB [tuple of true :: spec.zero n] bs) i.
          by admit.
        rewrite {1}/adcB /adcBmain /=.
        rewrite !tuple.beheadCons !tuple.theadCons /=.
        by admit.
      rewrite /spec.repr.
      apply/setP=> y; rewrite !inE.
      have Hy: y = ord0 \/ y = inord y.-1.+1 by admit.
      case Hy.
      + (* y = ord0 *)
        move ->.
        rewrite /getBit ltn0 andbF !orbF /=.
        rewrite /set_next_g.
        case: arg_minP=> //.
        + move=> i /andP[_ Hi] _.
          apply negbTE.
          by rewrite neq_ltn Hi.
      + (* y = inord z.+1 *)
        move ->.
        have ->: getBit [tuple of false :: addB [tuple of true :: spec.zero n] bs] (@inord n.+1 y.-1.+1)
               = getBit (addB [tuple of true :: spec.zero n] bs) (@inord n.+1 y.-1).
          by admit.
        set E' := [set x : 'I_n.+1 | inord(x.+1) \in E].
        set f' := @inord n f.
        set x' := @ord0 n.
        have HI': spec.repr (addB [tuple of true :: spec.zero n] bs) (set_next_g E' f' x' |: [set y in E' | y < x'] :|: [set y in E' | set_next_g E' f' x' < y]).
          apply HI.
          by apply (spec.repr_rec (b := b)).
          by admit. (* Trivial *)
          admit.
          admit.
        move: (HI bs [tuple of true :: spec.zero n] [set x : 'I_n.+1 | inord(x.+1) \in E] ord0 (inord f))=> HI1.
        rewrite {3}/spec.repr in HI1.
        admit. (* Apply HI *)
    + (* b' = false *)
      have ->: addB [tuple of false :: bs'] [tuple of b :: bs] = [tuple of b :: (addB bs' bs)].
        by admit.
      admit.
Admitted.

Lemma ripple_repr:
  forall i j S x f, machine_repr i S -> machine_repr j [set x] -> x \in S -> set_isNext_g S f x ->
    machine_repr (add j i) ((set_next_g S f x) |: [set y in S | y < x] :|: [set y in S | y > set_next_g S f x]).
Proof.
  move=> i j S x f [bv [r_native r_set]] [bv' [r_native' r_set']] Hx1 Hx2.
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
    rewrite (eq_pick (Q := [pred i0 | (i0 \notin S) && (set_min S e < i0) & [
               forall (j | (j \notin S) && (set_min S e < j)),
                 i0 <= j]])) //.
    move=> x /=.
    have Heq: forall x, [exists y, (y \in S) && (y < x)] = (set_min S e < x).
      move=> x0.
      rewrite /set_min.
      case: arg_minP=> //= j Hj Hj'.
      case Hx: (j < x0).
      + apply/existsP.
        exists j.
        by rewrite Hj Hx.
      + apply negbTE; rewrite negb_exists.
        apply/forallP=> y.
        rewrite negb_and.
        case Hy: (y \in S)=> //=.
        + move: (Hj' y Hy)=> Hy'.
          rewrite -leqNgt.
          apply (leq_trans (n := j))=> //.
          by rewrite leqNgt Hx.
    rewrite /set_isNext Heq.
    have ->: [forall (j | (j \notin S) && [exists y, (y \in S) && (y < j)]), x <= j] = [forall (j | (j \notin S) && (set_min S e < j)), x <= j].
      apply eq_forallb=> y.
      by rewrite Heq.
    rewrite //.
  move=> Hnext.
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
  apply ripple_repr=> //.
  apply keep_min_repr=> //.
  rewrite /set_min.
  case: arg_minP=> //.
  move: Hf=> /andP [Hf1 /existsP [y /andP [Hy1 Hy2]]].
  apply/andP; split=> //.
  apply (leq_ltn_trans (n := y))=> //.
  rewrite /set_min.
  case: arg_minP=> //.
  move=> x Hx /(_ y) Hy.
  by apply Hy.
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

Cd "examples/enum_parts".

Require Import ExtrOcamlBasic.

Extraction "enum_parts.ml" enumNext.

Cd "../..".
