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

Definition set_next (S: {set 'I_wordsize}) := [arg min_(x < ord0 | ((x \notin S) && [exists y, (y \in S) && (y < x)])) x].

Definition set_min (S: {set 'I_wordsize}) e := [arg min_(x < e in S) x].

Definition enumNext_set (S: {set 'I_wordsize}) e (H: e \in S) :=
  let s_min := set_min S e in
  let s_next := set_next S in
  [set s_next] :|: [set x in S | x > s_next] :|: (if s_next >= s_min + 2 then [set x in 'I_wordsize | x <= (s_next - s_min - 2)] else set0).

(* TODO: move to repr_op *)
Lemma srn_repr:
  forall i E s, machine_repr i E ->
    machine_repr (lsr i (toInt s)) [set i : 'I_wordsize | i < wordsize - s & @inord wordsize.-1 (i + s) \in E].
Proof.
Admitted.

Definition set_next_g {n} (S: {set 'I_n.+1}) x := [arg min_(y < ord0 | ((y \notin S) && (y > x))) y].

Lemma ripple_repr_1:
  forall n (bs: BITS n.+1) bs' E x, spec.repr bs E -> spec.repr bs' [set x] -> x \in E ->
    spec.repr (addB bs' bs) ((set_next_g E x) |: [set y in E | y < x] :|: [set y in E | y > set_next_g E x]).
Proof.
Admitted.

Lemma ripple_repr:
  forall i j S x, machine_repr i S -> machine_repr j [set x] -> x \in S ->
    machine_repr (add j i) ((set_next_g S x) |: [set y in S | y < x] :|: [set y in S | y > set_next_g S x]).
Proof.
  move=> i j S x [bv [r_native r_set]] [bv' [r_native' r_set']] Hx.
  exists (addB bv' bv); split.
  apply add_repr=> //.
  by apply ripple_repr_1.
Qed.  

Lemma enumNext_correct (i: Int32) (S: {set 'I_wordsize}) e (H: e \in S) :
  set_next S <> ord0 ->
  machine_repr i S -> machine_repr (enumNext i) (enumNext_set S e H).
Proof.
move=> Hnext Hi.
have repr_ripple: machine_repr (add (keep_min i) i)
     (set_next S |: [set x0 in S | set_next S < x0]).
  have ->: (set_next S |: [set x0 in S | set_next S < x0]) = ((set_next_g S (set_min S e)) |: [set y in S | y < (set_min S e)] :|: [set y in S | y > set_next_g S (set_min S e)]).
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
    rewrite setU0.
    have ->: set_next S = set_next_g S (set_min S e).
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
      rewrite Heq.
      have ->: [forall (j | (j \notin S) && [exists y, (y \in S) && (y < j)]), x <= j] = [forall (j | (j \notin S) && (set_min S e < j)), x <= j].
        apply eq_forallb=> y.
        by rewrite Heq.
      rewrite //.
      rewrite //.
  apply ripple_repr=> //.
  apply keep_min_repr=> //.
  rewrite /set_min.
  case: arg_minP=> //.
apply union_repr=> //.
have ->: add (toInt 2) (ntz i) = toInt (2 + set_min S e).
  by admit.
case: ifP=> Hnext'.
have ->: [set x0 in 'I_wordsize | x0 <= set_next S - set_min S e - 2] =
[set i : 'I_wordsize | i < wordsize - (2 + set_min S e) & @inord wordsize.-1 (i + (2 + set_min S e)) \in ([set set_next S] :|: [set x in S | x < set_next S])].
  apply/setP=> x; rewrite !inE.
  rewrite andbC andbT.
  rewrite [in _ || (_ && _)]andb_idl.
  rewrite -leq_eqVlt.
  case Hx: (x < wordsize - (2 + set_min S e)).
  + have Hx': x < wordsize.
    apply (leq_trans (n := wordsize - (2 + set_min S e)))=> //.
    apply leq_subr.
    rewrite andbC andbT inordK.
    have {2}->: set_next S = inord (set_next S - set_min S e - 2 + (2 + set_min S e)).
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
    rewrite inordK.
    by rewrite leq_add2r.
    rewrite -subnDA.
    rewrite [set_min S e + 2]addnC.
    rewrite subnK=> //.
    by rewrite addnC.
    rewrite addnC.
    rewrite -ltn_subRL=> //.
  + rewrite andbC andbF.
    rewrite leqNgt.
    apply negbF.
    rewrite ltnNge in Hx.
    have Hx': wordsize - (2 + set_min S e) <= x by apply negbFE; apply Hx.
    apply (leq_trans (n := wordsize - (2 + set_min S e)))=> //.
    rewrite -subnDA addnC.
    apply ltn_sub2r=> //.
    rewrite addnC.
    apply (leq_ltn_trans (n := set_next S))=> //.
  admit. (* if set_min S e <= i < set_next S, then i \in S *)
apply srn_repr.
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
  move: Hnext.
  rewrite /set_next /arg_min.
  case: pickP=> [y //= Ha _ /eqP->|//].
  by move/andP: Ha => [/andP [-> _] _].
apply symdiff_repr=> //.
admit. (* Case where the shift gives set0 *)
Admitted.

Cd "examples/enum_parts".

Require Import ExtrOcamlBasic.

Extraction "enum_parts.ml" enumNext.

Cd "../..".
