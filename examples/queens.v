From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Require Import bineqs repr_op.

Lemma fromInt63_elim:
  forall x, toInt63 (fromInt63 x) = x.
Proof.
Admitted.

Axiom ladd_repr:
  forall x y, BitsRepr.ladd (toInt63 x) (toInt63 y) = toInt63 (x + y).

(* ladd_repr2 can be proven from ladd_repr, but not the other way
Lemma ladd_repr2:
  forall x y, BitsRepr.ladd x y = toInt63 (fromInt63 x + fromInt63 y).
Proof.
move=> x y.
by rewrite ladd_repr !fromInt63_elim.
Qed.
*)

Lemma fromInt63_zero:
  fromInt63 BitsRepr.zero = 0.
Proof.
  rewrite fromInt63_def (BitsRepr.fromInt63_repr _ #0).
  rewrite toNat_fromNatBounded //.
  exact: BitsRepr.zero_repr.
Qed.

Lemma fromInt63_one:
  fromInt63 BitsRepr.one = 1.
Proof.
  rewrite fromInt63_def (BitsRepr.fromInt63_repr _ #1).
  rewrite toNat_fromNatBounded //.
  exact: BitsRepr.one_repr.
Qed.

Record pos := mkPos { ld: BitsRepr.Int63; 
                      col: BitsRepr.Int63;
                      rd: BitsRepr.Int63;
                      full: BitsRepr.Int63;
                      poss: BitsRepr.Int63;
                      curCount: BitsRepr.Int63;
                      mode: bool }.

Definition pos_order (p1 p2: pos): Prop := (* p1 < p2 <-> ... *)
      (fromInt63 (col p1) > fromInt63 (col p2))
   || ((fromInt63 (col p1) == fromInt63 (col p2))
       && (((mode p1) < (mode p2))
        || (((mode p1) == (mode p2))
           && (fromInt63 (poss p1) < fromInt63 (poss p2))))).

Theorem nqueens_wf : well_founded pos_order. Admitted.

(* TODO: these are true only if bit is not in col / is in poss *)
Lemma fromInt63_1: forall st bit, fromInt63 (col st) < fromInt63 (BitsRepr.lor (col st) bit).
Admitted.

Lemma fromInt63_2: forall st bit, fromInt63 (BitsRepr.land (poss st) (BitsRepr.lnot bit)) < fromInt63 (poss st).
Admitted.

Definition countNQueensAux: pos -> BitsRepr.Int63.
  refine (Fix nqueens_wf (fun _ => BitsRepr.Int63)
    (fun (st: pos) (countNQueensAux: forall st': pos, pos_order st' st -> BitsRepr.Int63) =>
  match (mode st) as x return mode st = x -> _ with
    | true => fun H =>
      if (BitsRepr.leq (col st) (full st)) then
        BitsRepr.one
      else
        let poss := BitsRepr.lnot (BitsRepr.lor (BitsRepr.lor (ld st) (rd st)) (col st)) in
        countNQueensAux (mkPos (ld st) (col st) (rd st) (full st) poss BitsRepr.zero false) _
    | false => fun H =>
      if (BitsRepr.leq (BitsRepr.land (poss st) (full st)) BitsRepr.zero) then
        curCount st
      else (
          let bit := BitsRepr.land (poss st) (BitsRepr.lneg (poss st)) in
          let count := countNQueensAux (mkPos
                         (BitsRepr.lsr (BitsRepr.lor (ld st) bit) BitsRepr.one)
                         (BitsRepr.lor (col st) bit)
                         (BitsRepr.lsl (BitsRepr.lor (rd st) bit) BitsRepr.one)
                         (full st) BitsRepr.zero BitsRepr.zero true) _ in
          countNQueensAux (mkPos
            (ld st) (col st) (rd st) (full st)
            (BitsRepr.land (poss st) (BitsRepr.lnot bit))
            (BitsRepr.ladd (curCount st) count) false) _
      )
  end Logic.eq_refl)).
  by rewrite /pos_order /= H !eq_refl /= orbT.
  by rewrite /pos_order fromInt63_1.
  by rewrite /pos_order H eq_refl fromInt63_2 orbC.
Qed.

Definition countNQueens (n: nat)
  := countNQueensAux (mkPos BitsRepr.zero BitsRepr.zero BitsRepr.zero (BitsRepr.ldec (BitsRepr.lsl BitsRepr.one (toInt63 n))) BitsRepr.zero BitsRepr.zero true).

Definition get_coord (n: nat) (B: BitsRepr.wordsize.-tuple (BitsRepr.wordsize.-tuple bool)) (x: 'I_BitsRepr.wordsize) (y: 'I_BitsRepr.wordsize) := tnth (tnth B x) y.

Definition is_complete n B : bool :=
  [forall k : 'I_BitsRepr.wordsize, (k < n) ==>
    [exists k', get_coord n B k' k == true]].

Definition is_correct cur n B :=
  [forall i : 'I_BitsRepr.wordsize, forall i' : 'I_BitsRepr.wordsize,
   (get_coord n B i i') ==> (i < n) && (i' < cur)
   && [forall j : 'I_BitsRepr.wordsize, forall j' : 'I_BitsRepr.wordsize,
    ~~ ((i == j) && (i' == j')) ==> (get_coord n B j j') ==>
    (i != j) && (i' != j') (* Not on the same horizontal / vertical line *)
    && (i + j' != j + i') (* Not on the same right diagonal *)
    && (i + i' != j + j')]]. (* Not on the same left diagonal *)

Definition valid_pos n := [set B | is_complete n B && is_correct n n B].

Definition make_ld n B i' := [set i : 'I_BitsRepr.wordsize | [exists j : 'I_BitsRepr.wordsize, exists j' : 'I_BitsRepr.wordsize, (get_coord n B j j') && (i + i' == j + j')]].

Definition repr_ld n B i' ld
  := native_repr ld (make_ld n B i').

Definition make_col n B := [set i : 'I_BitsRepr.wordsize | [exists i' : 'I_BitsRepr.wordsize,
       get_coord n B i i']].

Definition repr_col n B col
  := native_repr col (make_col n B).

Definition make_rd n B i'
  := [set i : 'I_BitsRepr.wordsize | [exists j : 'I_BitsRepr.wordsize, exists j' : 'I_BitsRepr.wordsize,
     (get_coord n B j j') && (i + j' == j + i')]].

Definition repr_rd n B i' rd
  := native_repr rd (make_rd n B i').

Definition repr_full n full
  := native_repr full [set x : 'I_BitsRepr.wordsize | x < n].

Definition board_included n B B' := [forall x, forall y, get_coord n B x y ==> get_coord n B' x y].

Definition empty_board := [tuple [tuple false | i < BitsRepr.wordsize] | i < BitsRepr.wordsize].

Definition board_possible n (P: {set ordinal_finType BitsRepr.wordsize}) B' i' := [forall i, get_coord n B' i i' ==> (i \in P)].

Record repr_queen {n B} {curLine: 'I_BitsRepr.wordsize} {ld rd col full} :=
  { line_val: nat_of_ord curLine = #|make_col n B|;
    correct: is_correct curLine n B;
    complete: is_complete curLine B;
    r_ld: repr_ld n B curLine ld;
    r_rd: repr_rd n B curLine rd;
    r_col: repr_col n B col;
    r_full: repr_full n full }.

Record repr_poss {n B curLine P poss} :=
  { poss_repr: native_repr poss P;
    poss_ld: P \subset (~: make_ld n B curLine);
    poss_rd: P \subset (~: make_rd n B curLine);
    poss_col: P \subset (~: make_col n B) }.

Record fuel_correct {n curLine} {P: {set 'I_BitsRepr.wordsize}} {fuel} :=
  { fuel_pos: fuel > 0;
    fuel_inLine: (forall x : 'I_BitsRepr.wordsize, x < n /\ x \in P ->
                  fuel >= (2 * n * (n - curLine) - [arg min_(k < x in P) k]).+1);
    fuel_gt1: fuel.-1 > 0 }.

Lemma size_full (n: nat) : n < BitsRepr.wordsize ->
  n = #|[set x : 'I_BitsRepr.wordsize | x < n]|.
Proof.
  elim: n=> [|n IHn] ltn_n.
  + (* n = 0 *)
    have ->: [set x : 'I_BitsRepr.wordsize | x < 0] = set0.
      rewrite -setP /eq_mem=> i.
      by rewrite in_set //.
    by rewrite cards0.
  + (* n ~ n.+1 *)
    have ltn'_n: n < BitsRepr.wordsize.
      by apply (ltn_trans (n := n.+1)).
    have ->: [set x : 'I_BitsRepr.wordsize | x < n.+1] = (inord n) |: [set x : 'I_BitsRepr.wordsize | x < n].
      rewrite -setP /eq_mem=> i.
      rewrite !in_set ltnS leq_eqVlt.
      have ->: (i == @inord BitsRepr.wordsize.-1 n) = (nat_of_ord i == n).
        apply/eqP.
        case H: (nat_of_ord i == n).
        + (* i == n *)
          move/eqP: H => H.
          apply ord_inj.
          by rewrite H inordK.
        + (* i <> n *)
          move=> Habs.
          have Habs': nat_of_ord i == n.
            apply/eqP.
            by rewrite Habs inordK.
          by rewrite Habs' in H.
        by trivial.
    rewrite cardsU1 -IHn=> //.
    have ->: (@inord 62 n \notin [set x : 'I_BitsRepr.wordsize | x < n]).
      rewrite in_set inordK=> //.
      by rewrite ltnn.
    by rewrite -add1n.
Qed.

Lemma from_correct: forall n cur i i' B, is_correct cur n B -> get_coord n B i i' ->
    (i < n) /\ (i' < cur) /\
      forall j j', (~~ ((i == j) && (i' == j'))) ==> (get_coord n B j j') ==>
        (i != j) && (i' != j') && (i + j' != j + i') && (i + i' != j + j').
  move=> n cur i i' B Hcorr Hii'.
  rewrite /is_correct in Hcorr.
  move/forallP: Hcorr=> Hcorr.
  move: (Hcorr i)=> /forallP Hcorr1.
  move: (Hcorr1 i')=> Hcorr2.
  rewrite Hii' /= in Hcorr2.
  move/andP: Hcorr2=> [/andP [HcorrA HcorrB] HcorrC].
  split.
  exact: HcorrA.
  split.
  exact: HcorrB.
  move=> j j'.
  move/forallP: HcorrC=> HcorrC.
  move: (HcorrC j)=> /forallP HcorrCj.
  by exact: (HcorrCj j').
Qed.

Lemma from_complete: forall n B, is_complete n B ->
  forall (k: 'I_BitsRepr.wordsize), k < n -> exists k', get_coord n B k' k.
Proof.
  move=> n B Hcompl k ltn_k.
  rewrite /is_complete in Hcompl.
  move/forallP: Hcompl=> Hcompl.
  move: (Hcompl k)=> Hcomplk.
  rewrite ltn_k implyTb in Hcomplk.
  move/existsP: Hcomplk=> [k' /eqP Hk'].
  exists k'.
  by rewrite Hk'.
Qed.

Lemma from_included: forall n B i j j', board_included n B i -> get_coord n B j j' -> get_coord n i j j'.
  move=> n B i j j' Hincl Hjj'.
  rewrite /board_included in Hincl.
  move/forallP: Hincl=> Hincl.
  move: (Hincl j)=> /forallP Hinclj.
  move: (Hinclj j')=> Hincljj'.
  by rewrite Hjj' /= in Hincljj'.
Qed.

Lemma from_possible: forall n (P: {set 'I_BitsRepr.wordsize}) B' i', board_possible n P B' i' ->
  forall i, get_coord n B' i i' -> i \in P.
Proof.
  move=> n P B' i' Hposs i Hii'.
  rewrite /board_possible in Hposs.
  move/forallP: Hposs=> Hposs.
  move: (Hposs i)=> Hpossi.
  by rewrite Hii' implyTb in Hpossi.
Qed.

Lemma nextLine_correct n B (curLine: 'I_BitsRepr.wordsize) (P: {set 'I_BitsRepr.wordsize}) poss ld rd col full x (ltn_ScurLine: curLine.+1 < BitsRepr.wordsize):
  let min := [arg min_(k < x in P) k] in
  let B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize] in
  @repr_poss n B curLine P poss ->
  @repr_queen n B curLine ld rd col full ->
  x \in P ->
  x < n ->
  min \in P ->
    is_correct (Ordinal ltn_ScurLine) n B'.
Proof.
  move=> min B' HP HB Hx ltn_x HminP.
  rewrite /is_correct.
  apply/forallP=> a.
  apply/forallP=> b.
  apply/implyP=> Hab.
  have Hmincorr: forall j j', ~~ ((min == j) && (curLine == j')) -> get_coord n B' j j' ->
    (min != j) && (curLine != j') && (min + j' != j + curLine) && (min + curLine != j + j').
    move=> j j' Hjj'1 Hjj'2.
    have Hjj'3: get_coord n B j j'.
      rewrite /get_coord /B' !tnth_mktuple in Hjj'2.
      have Hsym1: (j == min) = (min == j) by exact: eq_sym.
      have Hsym2: (j' == curLine) = (curLine == j') by exact: eq_sym.
      apply negbTE in Hjj'1.
      rewrite Hsym1 Hsym2 in Hjj'2.
      by rewrite Hjj'1 in Hjj'2.
    apply/andP.
    split.
    apply/andP.
    split.
    apply/andP.
    split.
    (* Horizontal *)
    have Hmincol: min \in (~: make_col n B).
      move/subsetP: (poss_col HP)=> HPcol.
      by apply: (HPcol min).
    rewrite /make_col !in_set negb_exists in Hmincol.
    move/forallP: Hmincol=> Hmincol.
    case Hj: (min == j)=> //=.
    move: (Hmincol j')=> Habs.
    move/eqP: Hj=>Hj.
    rewrite -Hj in Hjj'3.
    by rewrite Hjj'3 in Habs.
    (* Vertical *)
    move: (from_correct n curLine j j' B (correct HB) Hjj'3)=> [_ [Hltn _]].
    by rewrite neq_ltn Hltn orbT.
    (* TODO: factorize (Ltac?) *)
    (* rd *)
    have Hminrd: min \in (~: make_rd n B curLine).
      move/subsetP: (poss_rd HP)=> HPrd.
      by apply: (HPrd min).
    rewrite /make_rd !in_set negb_exists in Hminrd.
    move/forallP: Hminrd=> Hminrd.
    move: (Hminrd j)=> Hminrd1.
    rewrite negb_exists in Hminrd1.
    move/forallP: Hminrd1=> Hminrd1.
    move: (Hminrd1 j')=> Hminrd2.
    by rewrite Hjj'3 andbC andbT in Hminrd2.
    (* ld *)
    have Hminld: min \in (~: make_ld n B curLine).
      move/subsetP: (poss_ld HP)=> HPld.
      by apply: (HPld min).
    rewrite /make_ld !in_set negb_exists in Hminld.
    move/forallP: Hminld=> Hminld.
    move: (Hminld j)=> Hminld1.
    rewrite negb_exists in Hminld1.
    move/forallP: Hminld1=> Hminld1.
    move: (Hminld1 j')=> Hminld2.
    by rewrite Hjj'3 andbC andbT in Hminld2.

  case Hmin: ((a == min) && (b == curLine)).
  + (* (a == min) && (b == curLine) *)
    move/andP: Hmin=> [/eqP Ha /eqP Hb].
    rewrite !Ha !Hb.
    apply/andP.
    split.
    apply/andP.
    split.
    rewrite /min.
    case: arg_minP=> //.
    move=> i iP le_i.
    move: (le_i x Hx)=> Hi.
    by apply (leq_ltn_trans (n := x)).
    rewrite //.
    apply/forallP=> j.
    apply/forallP=> j'.
    apply/implyP=> Hjj'.
    apply/implyP=> Hjj'2.
    exact: (Hmincorr j j' Hjj' Hjj'2).
  + (* (a <> min) || (b <> curLine) *)
    have Hab': get_coord n B a b.
      by rewrite /get_coord /B' !tnth_mktuple Hmin in Hab.
    apply/andP.
    split.
    apply/andP.
    split.
    by move: (from_correct n curLine a b B (correct HB) Hab')=> [ltn_a _].
    move: (from_correct n curLine a b B (correct HB) Hab')=> [_ [ltn_b _]].
    by apply (ltn_trans (n := curLine))=> //.
    apply/forallP=> j.
    apply/forallP=> j'.
    apply/implyP=> Hjj'.
    apply/implyP=> Hjj'2.
    case Hmin': ((j == min) && (j' == curLine)).
    - (* (j == min) && (j' == curLine) *)
      move/andP: Hmin'=> [/eqP Hj /eqP Hj'].
      rewrite Hj Hj'.
      move: (Hmincorr a b).
      rewrite [min == a]eq_sym [curLine == b]eq_sym
              [min + b == a + curLine]eq_sym [a + b == min + curLine]eq_sym
              Hmin /= Hab.
      move=> Hcorr.
      exact: Hcorr.
    - (* j <> min || j' <> curLine *)
      have Hjj'3: get_coord n B j j'.
        by rewrite /get_coord /B' !tnth_mktuple Hmin' in Hjj'2.
      move: (from_correct n curLine a b B (correct HB) Hab')=> [_ [_ Hcorr]].
      move: (Hcorr j j')=> Hcorr1.
      by rewrite Hjj' Hjj'3 /= in Hcorr1.
Qed.

Lemma nextLine_complete n B curLine ld rd col full min:
  let B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize] in
  @repr_queen n B curLine ld rd col full ->
  is_complete curLine.+1 B'.
Proof.
  move=> B' HB.
  rewrite /is_complete.
  apply/forallP=> j.
  apply/implyP=> ltn_j.
  case Hj: (j == curLine).
  + (* j == curLine *)
    apply/existsP.
    exists min.
    by rewrite /get_coord !tnth_mktuple Hj eq_refl.
  + (* j <> curLine *)
    have Hj': j < curLine.
      rewrite ltn_neqAle.
      apply negbT in Hj.
      by rewrite Hj andbC andbT -(leq_add2r 1) !addn1.
    move: (from_complete curLine B (complete HB) j Hj')=> [k' /eqP Hk'].
    apply/existsP.
    exists k'.
    by rewrite /get_coord /B' !tnth_mktuple Hj andbF.
Qed.

Lemma nextLine_P n B curLine (P: {set 'I_BitsRepr.wordsize}) poss (x: 'I_BitsRepr.wordsize):
  let min := [arg min_(k < x in P) k] in
  let P' := P :\ min in
  let bit := BitsRepr.land poss (BitsRepr.lneg poss) in
  let poss' := BitsRepr.land poss (BitsRepr.lnot bit) in
  x \in P ->
  @repr_poss n B curLine P poss ->
  @repr_poss n B curLine P' poss'.
Proof.
  move=> min P' bit poss' Hx HP.
  split; try (rewrite /P';
             apply (subset_trans (B := pred_of_set P))=> //;
             [rewrite subD1set|apply HP])=> //.
  (* P' *)
  rewrite /P' setDE.
  apply inter_repr.
  apply HP.
  apply compl_repr.
  apply keep_min_repr=> //.
  by apply HP.
Qed.

Lemma nextLine_ld n B (curLine: 'I_BitsRepr.wordsize) ld rd col full poss (P: {set 'I_BitsRepr.wordsize}) x (ltn_ScurLine: curLine.+1 < BitsRepr.wordsize):
  let bit := BitsRepr.land poss (BitsRepr.lneg poss) in
  let min := [arg min_(k < x in P) k] in
  let B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize] in
  let ld' := BitsRepr.lsr (BitsRepr.lor ld bit) BitsRepr.one in
  n < BitsRepr.wordsize ->
  x \in P ->
  @repr_queen n B curLine ld rd col full ->
  @repr_poss n B curLine P poss ->
  is_correct (Ordinal ltn_ScurLine) n B' ->
  repr_ld n B' (Ordinal ltn_ScurLine) ld'.
Proof.
  move=> bit min B' ld' ltn_n Hx HB HP HB'cor.
  rewrite /repr_ld.
  have ->: (make_ld n B' (Ordinal ltn_ScurLine)) = [set i : 'I_BitsRepr.wordsize | (i < BitsRepr.wordsize.-1) && (inord i.+1 \in (make_ld n B' curLine))].
    rewrite /make_ld -setP /eq_mem=> i.
    rewrite !in_set.
    have Habs: i.+1 >= n -> [exists j, exists j', get_coord n B' j j' && (i + curLine.+1 == j + j')] = false.
      move=> leq_n.
      apply negbTE.
      rewrite negb_exists.
      apply/forallP=> j.
      rewrite negb_exists.
      apply/forallP=> j'.
      rewrite negb_and.
      rewrite neq_ltn.
      case Hjj': (get_coord n B' j j')=> //.
      have ->: j + j' < i + curLine.+1.
        rewrite -[curLine.+1]add1n addnA addn1.
        move: (from_correct n (Ordinal ltn_ScurLine) j j' B' HB'cor Hjj')=> [Hj [Hj' _]].
        apply (leq_trans (n := n + curLine)).
        apply (leq_ltn_trans (n := j + curLine)).
        rewrite leq_add2l=> //.
        rewrite ltn_add2r=> //.
        rewrite leq_add2r=> //.
      by rewrite orbT orbT.
    case ltn'_i: (i < BitsRepr.wordsize .-1).
    + (* i < BitsRepr.wordsize .-1 *)
      rewrite inordK.
      have ->: i + curLine.+1 = i.+1 + curLine.
        by rewrite -add1n addnA addn1 //.
      rewrite //.
      rewrite -[i.+1]addn1 -[63]addn1 ltn_add2r.
      by apply ltn'_i.
    + (* i >= BitsRepr.wordsize .-1 *)
      have Hi: i.+1 >= n.
        apply (leq_trans (n := BitsRepr.wordsize))=> //.
        rewrite leq_eqVlt ltn_n orbT //.
        rewrite -(leq_add2r 1) !addn1 /= in ltn'_i.
        by rewrite leqNgt ltn'_i.
      by rewrite (Habs Hi).
  apply sr_repr.
  have ->: make_ld n B' curLine = (make_ld n B curLine) :|: [set min].
    rewrite /make_ld -setP /eq_mem=> i.
    rewrite in_setU !in_set.
    case Hi: (i == min).
    + (* i == min *)
      rewrite orbT.
      apply/existsP.
      exists min.
      apply/existsP.
      exists curLine.
      rewrite /B' /get_coord !tnth_mktuple !eq_refl /=.
      by move/eqP: Hi ->.
    + (* i <> min *)
      rewrite orbF.
      case HcurLine0: [exists j, exists j', get_coord n B j j' && (i + curLine == j + j')].
      + (* true *)
        move/existsP: HcurLine0=> [j /existsP [j' /andP [Hjj'1 Hjj'2]]].
        apply/existsP.
        exists j.
        apply/existsP.
        exists j'.
        rewrite /get_coord in Hjj'1.
        by rewrite /B' /get_coord !tnth_mktuple Hjj'1 if_same Hjj'2.
      + (* false *)
        apply negbTE.
        rewrite negb_exists.
        apply/forallP=> j.
        rewrite negb_exists.
        apply/forallP=> j'.
        apply negbT in HcurLine0.
        rewrite negb_exists in HcurLine0.
        move/forallP: HcurLine0=> HcurLine0.
        move: (HcurLine0 j)=> HcurLine1.
        rewrite negb_exists in HcurLine1.
        move/forallP: HcurLine1=> HcurLine1.
        move: (HcurLine1 j')=> HcurLine2.
        rewrite /B' /get_coord !tnth_mktuple.
        case Hjj': ((j == min) && (j' == curLine)).
        + (* j = min & j' = curLine *)
          rewrite andbC andbT.
          move/andP: Hjj'=> [/eqP Hj /eqP Hj'].
          rewrite Hj Hj' eqn_add2r.
          by apply negbT in Hi.
        + (* j <> min || j' <> curLine *)
          by rewrite /get_coord in HcurLine2.
  apply union_repr=> //.
  apply HB.
  apply keep_min_repr=> //.
  apply HP.
Qed.

Lemma nextLine_rd n B (curLine: 'I_BitsRepr.wordsize) ld rd col full poss (P: {set 'I_BitsRepr.wordsize}) x (ltn_ScurLine: curLine.+1 < BitsRepr.wordsize):
  let bit := BitsRepr.land poss (BitsRepr.lneg poss) in
  let min := [arg min_(k < x in P) k] in
  let B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize] in
  let rd' := BitsRepr.lsl (BitsRepr.lor rd bit) BitsRepr.one in
  x \in P ->
  @repr_queen n B curLine ld rd col full ->
  @repr_poss n B curLine P poss ->
  is_correct (Ordinal ltn_ScurLine) n B' ->
  repr_rd n B' (Ordinal ltn_ScurLine) rd'.
Proof.
  move=> bit min B' rd' Hx HB HP HB'cor.
  rewrite /repr_rd.
  have ->: (make_rd n B' (Ordinal ltn_ScurLine)) = [set i : 'I_BitsRepr.wordsize | ((i > 0) && (inord i.-1 \in (make_rd n B' curLine)))].
    rewrite /make_rd -setP /eq_mem=> i.
    rewrite !in_set.
    case Hi: (i > 0)=> /=.
    + (* i > 0 *)
      rewrite inordK.
      have Heq: forall j j', (i.-1 + j' == j + curLine) = (i + j' == j + curLine.+1).
        move=> j j'.
        rewrite -(eqn_add2r 1).
        rewrite addnC addnA -subn1 subnKC=> //.
        by rewrite -addnA addn1.
      case Hex: [exists j, exists j', get_coord n B' j j' && (i + j' == j + curLine.+1)].
      + (* true *)
        move/existsP: Hex=> [j /existsP [j' /andP [Hjj'1 Hjj'2]]].
        symmetry.
        apply/existsP.
        exists j.
        apply/existsP.
        exists j'.
        rewrite Hjj'1.
        by rewrite (Heq j j').
      + (* false *)
        symmetry.
        apply negbTE.
        rewrite negb_exists.
        apply/forallP => j.
        rewrite negb_exists.
        apply/forallP=> j'.
        rewrite (Heq j j').
        apply negbT in Hex.
        rewrite negb_exists in Hex.
        move/forallP: Hex=> Hex.
        move: (Hex j)=> Hexj.
        rewrite negb_exists in Hexj.
        move/forallP: Hexj=> Hexj.
        by move: (Hexj j')=> Hexjj'.
      apply (ltn_trans (n := i)).
      rewrite prednK // => //.
      apply ltn_ord.
    + (* i <= 0 *)
      apply negbTE.
      rewrite negb_exists.
      apply/forallP=> j.
      rewrite negb_exists.
      apply/forallP=> j'.
      rewrite negb_and.
      case Hjj': (get_coord n B' j j')=> //=.
      rewrite neq_ltn.
      apply/orP; left.
      have ->: i = ord0.
        apply negbT in Hi.
        rewrite -eqn0Ngt in Hi.
        move/eqP: Hi=> Hi.
        apply ord_inj.
        by rewrite Hi.
      have ->: ord0 (n' := BitsRepr.wordsize.-1) + j' = j' by trivial.
      rewrite ltn_addl //.
      by move: (from_correct n (Ordinal ltn_ScurLine) j j' B' HB'cor Hjj')=> [_ [Hj' _]].
  apply sl_repr.
  have ->: make_rd n B' curLine = (make_rd n B curLine) :|: [set min].
    rewrite /make_rd -setP /eq_mem=> i.
    rewrite in_setU !in_set.
    case Hi: (i == min).
    + (* i == min *)
      rewrite orbT.
      apply/existsP.
      exists min.
      apply/existsP.
      exists curLine.
      rewrite /B' /get_coord !tnth_mktuple.
      have ->: min == min by trivial.
      have ->: curLine == curLine by trivial.
      move/eqP: Hi ->.
      by rewrite /=.
    + (* i <> min *)
      rewrite orbF.
      case HcurLine0: [exists j, exists j', get_coord n B j j' && (i + j' == j + curLine)].
      + (* true *)
        move/existsP: HcurLine0=> [j /existsP [j' /andP [Hjj'1 Hjj'2]]].
        apply/existsP.
        exists j.
        apply/existsP.
        exists j'.
        rewrite /get_coord in Hjj'1.
        by rewrite /B' /get_coord !tnth_mktuple Hjj'1 if_same Hjj'2.
      + (* false *)
        apply negbTE.
        rewrite negb_exists.
        apply/forallP=> j.
        rewrite negb_exists.
        apply/forallP=> j'.
        apply negbT in HcurLine0.
        rewrite negb_exists in HcurLine0.
        move/forallP: HcurLine0=> HcurLine0.
        move: (HcurLine0 j)=> HcurLine1.
        rewrite negb_exists in HcurLine1.
        move/forallP: HcurLine1=> HcurLine1.
        move: (HcurLine1 j')=> HcurLine2.
        rewrite /B' /get_coord !tnth_mktuple.
        case Hjj': ((j == min) && (j' == curLine)).
        + (* j = min & j' = curLine *)
          rewrite andbC andbT.
          move/andP: Hjj'=> [/eqP Hj /eqP Hj'].
          rewrite Hj Hj' eqn_add2r.
          by apply negbT in Hi.
        + (* j <> min || j' <> curLine *)
          by rewrite /get_coord in HcurLine2.
  apply union_repr=> //.
  apply HB.
  apply keep_min_repr=> //.
  by apply HP.
Qed.

Lemma nextLine_col n B curLine ld rd col full poss (P: {set 'I_BitsRepr.wordsize}) (x: 'I_BitsRepr.wordsize):
  let bit := BitsRepr.land poss (BitsRepr.lneg poss) in
  let min := [arg min_(k < x in P) k] in
  let B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize] in
  let col' := BitsRepr.lor col bit in
  x \in P ->
  @repr_queen n B curLine ld rd col full ->
  @repr_poss n B curLine P poss ->
  repr_col n B' col'.
Proof.
  move=> bit min B' col' Hx HB HP.
  rewrite /repr_col.
  have ->: make_col n B' = (make_col n B) :|: [set min].
    rewrite /make_col -setP /eq_mem=> i.
    rewrite in_setU !in_set.
    case Hi: (i == min).
    + (* i == min *)
      rewrite orbT.
      apply/existsP.
      exists curLine.
      rewrite /B' /get_coord !tnth_mktuple Hi /=.
      by have ->: curLine == curLine by trivial.
    + (* i <> min *)
      rewrite orbF.
      rewrite /B' {1}/get_coord !tnth_mktuple Hi /=.
      case HcurLine0: [exists curLine0, get_coord n B i curLine0].
      + (* [exists curLine0, get_coord n B i curLine0] *)
        move/existsP: HcurLine0=> [y Hy].
        apply/existsP.
        exists y.
        by rewrite tnth_mktuple.
      + (* ~~ [exists curLine0, get_coord n B i curLine0] *)
        apply negbT in HcurLine0.
        rewrite negb_exists in HcurLine0.
        move/forallP: HcurLine0=>HcurLine0.
        apply negbTE.
        rewrite negb_exists.
        apply/forallP=> y.
        rewrite tnth_mktuple.
        by apply (HcurLine0 y).
  apply union_repr=> //.
  apply HB.
  apply keep_min_repr=> //.
  by apply HP.
Qed.

Lemma nextLine_numCol n B (curLine: 'I_BitsRepr.wordsize) ld rd col full min (P: {set 'I_BitsRepr.wordsize}) poss (ltn_ScurLine: curLine.+1 < BitsRepr.wordsize) (HminP: min \in P):
  let B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize] in
  @repr_queen n B curLine ld rd col full ->
  @repr_poss n B curLine P poss ->
  #|make_col n B'| = Ordinal ltn_ScurLine.
Proof.
  move=> B' HB HP.
  have ->: make_col n B' = (make_col n B) :|: [set min].
    rewrite -setP /eq_mem=> i.
    rewrite /make_col in_setU !in_set.
    case Hi: (i == min).
    + (* i == min *)
      rewrite orbT.
      apply/existsP.
      exists curLine.
      rewrite /get_coord /B' !tnth_mktuple Hi /=.
      have ->: curLine == curLine by trivial.
      trivial.
    + (* i <> min *)
      rewrite orbF.
      case Hex: [exists curLine0, get_coord n B i curLine0].
      - (* exists curLine0, get_coord n B i curLine0 *)
        move/existsP: Hex=> [y Hy].
        apply/existsP.
        exists y.
        by rewrite /get_coord /B' !tnth_mktuple Hi andbC andbF Hy.
      - (* ~ exists curLine0, get_coord n B i curLine0 *)
        apply negbT in Hex.
        rewrite negb_exists in Hex.
        move/forallP: Hex=> Hex.
        apply negbTE.
        rewrite negb_exists.
        apply/forallP=> y.
        rewrite /get_coord /B' !tnth_mktuple Hi andbC andbF.
        by apply (Hex y).
  rewrite cardsU.
  have ->: make_col n B :&: [set min] = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_setI in_set1 in_set0.
    case Hi: (i == min).
    + (* i == min *)
      rewrite andbT.
      move/eqP: Hi ->.
      apply negbTE.
      rewrite -in_setC.
      move/subsetP: (poss_col HP)=> HPcol.
      by apply (HPcol min).
    + (* i <> min *)
      by rewrite andbF.
  by rewrite cards0 subn0 -(line_val HB) cards1 addn1.
Qed.

Lemma nextLine_splitCase n B curLine P min:
  let P' := P :\ min in
  let B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize] in
  let setA := [set B'0 in valid_pos n | board_included n B B'0 & board_possible n P' B'0 curLine] in
  let setB := [set B'0 in valid_pos n | board_included n B' B'0] in
  let setC := [set B'0 in valid_pos n | board_included n B B'0 & board_possible n P B'0 curLine] in
  min \in P ->
  setC = setA :|: setB /\ setA :&: setB = set0.
Proof.
  move=> P' B' setA setB setC HminP.
  split.
  rewrite -setP /eq_mem=> i.
  rewrite in_setU !in_set.
  rewrite -Bool.andb_orb_distrib_r.
  case Hicorr: (is_correct n n i).
  have ->: board_included n B i && board_possible n P i curLine
         = board_included n B i && board_possible n P' i curLine || board_included n B' i.
    have ->: board_included n B' i = board_included n B i && board_included n B' i.
      rewrite andb_idl // => Hi.
      rewrite /board_included.
      apply/forallP=> j.
      apply/forallP=> j'.
      apply/implyP=> Hjj'.
      rewrite /board_included in Hi.
      move/forallP: Hi=>Hi.
      move: (Hi j)=> /forallP Hij.
      move: (Hij j')=> /implyP Hijj'.
      have Hjj'1: get_coord n B' j j'.
        rewrite /B' /get_coord !tnth_mktuple.
        rewrite /get_coord in Hjj'.
        by rewrite Hjj' if_same.
      by rewrite (Hijj' Hjj'1).
    rewrite -Bool.andb_orb_distrib_r.
    case HBi: (board_included n B i)=> //=.
    have ->: board_possible n P i curLine = board_possible n P' i curLine || board_included n B' i.
      case HiP: (board_possible n P i curLine).
      + (* board_possible n P i curLine = true *)
        case HiP': (board_possible n P' i curLine)=> //=.
        rewrite /board_included.
        symmetry.
        apply/forallP=> x0.
        apply/forallP=> y0.
        apply/implyP=> HinB'.
        case Hmin: ((x0 == min) && (y0 == curLine)).
        + (* x0 == min && y0 == curLine is true *)
          move/existsP: HiP'=>[x' Hx'].
          rewrite negb_imply in Hx'.
          move/andP: Hx'=>[Hx1 Hx2].
          move: (from_possible n P i curLine HiP x' Hx1)=> HxP.
          have Hx': x' = min.
            apply/eqP.
            rewrite -in_set1.
            have ->: [set min] = P :\: P'.
              rewrite setDDr setDv set0U.
              symmetry.
              apply/setIidPr.
              by rewrite sub1set.
            by rewrite in_setD Hx2 HxP //.
          move/andP: Hmin=>[/eqP Hmin1 /eqP Hmin2].
          by rewrite Hmin1 Hmin2 -Hx' Hx1.
        + (* x0 == min && y0 == curLine is false *)
          rewrite /B' /get_coord !tnth_mktuple Hmin in HinB'.
          exact: (from_included n B i x0 y0 HBi HinB').
      + (* board_possible n P i curLine = false *)
        case HiP': (board_possible n P' i curLine).
        + (* board_possible n P' i curLine = true *)
          rewrite orbC orbT.
          have: board_possible n P i curLine = true.
            rewrite /board_possible.
            apply/forallP=> y.
            apply/implyP=> Hy.
            move: (from_possible n P' i curLine HiP' y Hy)=> Hy'.
            rewrite in_setD in Hy'.
            move: Hy'=> /andP [_ HyP] //.
          by rewrite HiP.
        + (* board_possible n P' i curLine = false *)
          have: board_included n B' i = false.
            rewrite /board_included.
            apply/forallP/forallP.
            rewrite negb_forall.
            apply/existsP.
            exists min.
            rewrite negb_forall.
            apply/existsP.
            exists curLine.
            rewrite negb_imply.
            rewrite {1}/get_coord /B' !tnth_mktuple !eq_refl /=.
            rewrite /board_possible in HiP.
            move/forallP: HiP=> /forallP HiP.
            rewrite negb_forall in HiP.
            move/existsP: HiP=> [j Hj].
            rewrite negb_imply in Hj.
            move: Hj=> /andP [Hj HjP].
            case Habs: (j == min).
            - (* j == min *)
              move/eqP: Habs=>Habs.
              rewrite Habs in HjP.
              exfalso.
              by rewrite HminP in HjP.
            - (* j <> min *)
              apply/negP=> Hmin.
              move: (from_correct n n j curLine i Hicorr Hj)=> [_ [_ Hicorr']].
              move: (Hicorr' min curLine)=> Hicorr''.
              rewrite Hmin implyTb Habs andbC andbF /= in Hicorr''.
              move: Hicorr''=> /andP [/andP [Habs' _] _].
              by move/eqP: Habs'.
          by rewrite //.
    by rewrite //.
  by rewrite //.
  by rewrite andbF andbC andbF andbC andbF.
  (* setA :&: setB = set0 *)
  rewrite -setP /eq_mem=> i.
  rewrite in_setI !in_set.
  case Hinc: (board_included n B' i) setB=> setB.
  + (* B' included in i *)
    case Hpos: (board_possible n P' i curLine).
    - (* (x, curLine) in i => x in P' *)
      exfalso.
      have Hmin: get_coord n i min curLine.
        move: (from_included n B' i min curLine Hinc)=> Hinc'.
        have Hmin: get_coord n B' min curLine.
          by rewrite /B' /get_coord !tnth_mktuple !eq_refl.
        exact: (Hinc' Hmin).
      move: (from_possible n P' i curLine Hpos min Hmin)=> Hpos'.
      rewrite in_setD in Hpos'.
      move/andP: Hpos'=> [Habs _].
      rewrite in_set1 in Habs.
      by move/eqP: Habs.
    - (* board_possible n P' i curLine = false *)
      by rewrite andbF andbF andbC andbF.
  + (* B' not included in i *)
    by rewrite !andbF.
Qed.

Lemma nextLine_end (n: nat) B (curLine: 'I_BitsRepr.wordsize) ld rd col full (HcurLine2: n = curLine):
  @repr_queen n B curLine ld rd col full ->
  1 = #|[set B' in valid_pos n | board_included n B B']|.
Proof.
  move=> HB.
  have ->: [set B' in valid_pos n | board_included n B B'] = [set B].
    rewrite -setP /eq_mem=> B'.
    rewrite !in_set.
    case HB': (B' == B).
    + (* B' = B *)
      move/eqP: HB' ->.
      have ->: is_complete n B.
        by rewrite HcurLine2; apply HB.
      rewrite {1}HcurLine2.
      rewrite (correct HB).
      have ->: board_included n B B = true.
        rewrite /board_included.
        apply/forallP=> x.
        apply/forallP=> y.
        by rewrite implybb.
      by rewrite /=.
    + (* B' <> B *)
      apply/andP/andP.
      apply/negP=> H'.
      move: H'=> /andP [/andP[H1 H2] H3].
      have Habs: B' = B.
        apply eq_from_tnth.
        rewrite /eqfun=> x.
        apply eq_from_tnth.
        rewrite /eqfun=> y.
        case Hxy: (tnth (tnth B x) y).
        - (* tnth (tnth B x) y = true *)
          exact: (from_included n B B' x y H3 Hxy).
        - (* tnth (tnth B x) y = false *)
          case Hy: (y < curLine).
          + (* y < curLine *)
            move: (from_complete curLine B (complete HB) y Hy)=> [k' Hk'].
            rewrite -HcurLine2 in Hk'.
            move: (from_included n B B' k' y H3 Hk')=> Hk'1.
            move: (from_correct n n k' y B' H2 Hk'1)=> [_ [_ Hcorr']].
            move: (Hcorr' x y)=> Hcorr''.
            rewrite eq_refl /= andbT andbF andbC andbF in Hcorr''.
            case Hk'x: (k' != x).
            + (* k' != x *)
              rewrite Hk'x implybF implyTb in Hcorr''.
              by apply negbTE.
            + (* k' == x *)
              apply negbT in Hk'x.
              move/negPn: Hk'x=> /eqP Hk'x.
              by rewrite Hk'x /get_coord Hxy in Hk'.
          + (* y >= curLine *)
            apply/negP=> Hxy'.
            move: (from_correct n n x y B' H2 Hxy')=> H2'.
            rewrite {2}HcurLine2 Hy /get_coord in H2'.
            by move: H2'=> [_ [Habs _]].
      rewrite Habs in HB'.
      move/eqP: HB'=>HB'.
      by rewrite //.
  by rewrite cards1.
Qed.

Lemma nextLine_oneCase n B (curLine: 'I_BitsRepr.wordsize) ld rd col full:
  let P := (~: (((make_ld n B curLine) :|: (make_rd n B curLine)) :|: (make_col n B))) in
  @repr_queen n B curLine ld rd col full ->
  [set B' in valid_pos n | board_included n B B' & board_possible n P B' curLine]
  = [set B' in valid_pos n | board_included n B B'].
Proof.
  move=> P HB.
  rewrite -setP /eq_mem=> i.
  rewrite !in_set.
  rewrite andbA.
  case Hi: (is_complete n i && is_correct n n i && board_included n B i).
  + (* is_complete n i && is_correct n n i && board_included n B i *)
    rewrite andbC andbT.
    move/andP: Hi=> [/andP[Hicompl Hicorr] HBi].
    rewrite /board_possible.
    apply/forallP=> x.
    apply/implyP=> HxcurLine.
    rewrite in_setC !in_setU.
    rewrite !negb_or.
    have ->: x \notin make_ld n B curLine.
      apply/negP=> Habs.
      rewrite /make_ld in_set in Habs.
      move/existsP: Habs=> [j /existsP [j' /andP [Hjj'1 Hjj'2]]].
      move: (from_correct n n x curLine i Hicorr HxcurLine)=> [_ [_ Hicorr2]].
      move: (Hicorr2 j j')=> Hicorr2'.
      move: (from_correct n curLine j j' B (correct HB) Hjj'1)=> [_ [Hj' _]].
      have Hj'2: (curLine == j') = false.
        apply negbTE.
        by rewrite neq_ltn Hj' orbT.
      move: (from_included n B i j j' HBi Hjj'1)=> HjB.
      rewrite Hj'2 andbF /= HjB /= in Hicorr2'.
      by rewrite Hjj'2 /= andbF in Hicorr2'.
    have ->: x \notin make_rd n B curLine.
      apply/negP=> Habs.
      rewrite /make_rd in_set in Habs.
      move/existsP: Habs=> [j /existsP [j' /andP [Hjj'1 Hjj'2]]].
      move: (from_correct n n x curLine i Hicorr HxcurLine)=> [_ [_ Hicorr2]].
      move: (Hicorr2 j j')=> Hicorr2'.
      move: (from_correct n curLine j j' B (correct HB) Hjj'1)=> [_ [Hj' _]].
      have Hj'2: (curLine == j') = false.
        apply negbTE.
        by rewrite neq_ltn Hj' orbT.
      move: (from_included n B i j j' HBi Hjj'1)=> HjB.
      rewrite Hj'2 andbF /= HjB /= in Hicorr2'.
      by rewrite Hjj'2 /= andbF in Hicorr2'.
    have ->: x \notin make_col n B.
      apply/negP=> Habs.
      rewrite /make_col in_set in Habs.
      move/existsP: Habs=> [j Hj].
      move: (from_correct n n x curLine i Hicorr HxcurLine)=> [_ [_ Hicorr2]].
      move: (Hicorr2 x j)=> Hicorr2'.
      move: (from_correct n curLine x j B (correct HB) Hj)=> [_ [Hj2 _]].
      rewrite eq_refl /= (from_included n B i x j HBi Hj) in Hicorr2'.
      have Hj2': (curLine == j) = false.
        apply negbTE.
        by rewrite neq_ltn Hj2 orbT.
      by rewrite Hj2' /= in Hicorr2'.
    by rewrite /=.
  + (* ~~ (is_complete n i && is_correct n n i && board_included n B i ) *)
    by rewrite andbC andbF.
Qed.

Lemma queens_correctInd (n: nat) : n > 0 -> n < BitsRepr.wordsize ->
    (forall poss ld col rd full B (curLine: 'I_BitsRepr.wordsize) curCount (P: {set 'I_BitsRepr.wordsize}),
    curLine < n ->
    @repr_queen n B curLine ld rd col full ->
     @repr_poss n B curLine P poss ->
       countNQueensAux (mkPos ld col rd full poss curCount false) =
         toInt63 (#|[set B' in (valid_pos n) | board_included n B B' && board_possible n P B' curLine]| + (fromInt63 curCount)))
    /\
    (forall ld col rd full B (curLine: 'I_BitsRepr.wordsize),
    @repr_queen n B curLine ld rd col full ->
      countNQueensAux (mkPos ld col rd full BitsRepr.zero BitsRepr.zero true) =
        toInt63 #|[set B' in (valid_pos n) | board_included n B B']|).
Proof.
Admitted.
(*
  move=> gtz_n ltn_n.
  split.
  move=> poss ld col rd full B curLine curCount P ltn_curLine Hqueen HP.
  rewrite /countNQueensAux.
  rewrite -/countNQueensAux.
  case Hend: (BitsRepr.leq (BitsRepr.land poss full) BitsRepr.zero).
  + (* (poss & full) == 0 *)
    rewrite (eq_repr _ _ [set x in P | x < n] set0) in Hend.
    move/eqP: Hend=> Hend.
    have H1: forall x : 'I_BitsRepr.wordsize, x \in P -> x >= n.
      move=> x Hx.
      case ltn_x: (n <= x)=> //.
      apply negbT in ltn_x.
      rewrite -ltnNge in ltn_x.
      have: x \in [set x in P | x < n] by rewrite in_set Hx ltn_x.
      by rewrite Hend in_set0.
    have ->: [set B' in valid_pos n | board_included n B B' & board_possible n P B' curLine] = set0.
      rewrite -setP /eq_mem=> B0.
      rewrite in_set in_set0 /board_possible /valid_pos in_set.
      apply/andP.
      move=> [/andP[Hcompl Hcor] /andP[_ Hposs]].
      move: (from_complete _ _ Hcompl curLine ltn_curLine)=> [i Hi].
      move: (from_possible _ _ _ _ Hposs i Hi)=> Hpossi.
      move: (H1 i Hpossi)=> Habsi.
      move: (from_correct _ _ i curLine _ Hcor Hi)=> [Habs2 _].
      rewrite ltnNge in Habs2.
      by rewrite Habsi // in Habs2.
    by rewrite cards0 add0n fromInt63_elim.
    rewrite setIdE.
    apply (inter_repr _ _ P [set x : 'I_BitsRepr.wordsize | x < n])=> //.
    apply HP.
    apply Hqueen.
    apply zero_repr.
  + (* (poss & full) != 0 *)
    rewrite (eq_repr _ _ [set x in P | x < n] set0) in Hend.
    move/eqP: Hend=> Hend.
    set bit := (BitsRepr.land poss (BitsRepr.lneg poss)).
    have: [exists x : 'I_BitsRepr.wordsize, (x < n) && (x \in P)].
      case Habs: [exists x : 'I_BitsRepr.wordsize, (x < n) && (x \in P)]=> //.
      apply negbT in Habs.
      rewrite negb_exists in Habs.
      move/forallP: Habs=> Habs.
      have Habs': [set x in P | x < n] = set0.
        rewrite -setP /eq_mem=> i.
        rewrite in_set in_set0 andbC.
        apply negbTE.
        by rewrite (Habs i).
      by rewrite Habs' in Hend.
    move/existsP=> [x /andP [ltn_x Hx]].
    set min := [arg min_(k < x in P) k].
    have HminP: min \in P.
      rewrite /min /arg_min.
      case: pickP=> y //=.
      by move/andP => [H1 _].
    have Hminn: min < n.
      rewrite /min.
      case: arg_minP=> //.
      move=> i Hi Hj.
      apply (leq_ltn_trans (n := x))=> //.
      by apply (Hj x)=> //.
    have Hminn': min < 2 * n * (n - curLine).
      apply (leq_trans (n := n)).
      apply Hminn.
      apply (leq_trans (n := 2 * n)).
      rewrite -{1}[n]mul1n leq_mul2r.
      have ->: 0 < 2 by trivial.
      rewrite orbT //.
      rewrite -{1}[2 * n]muln1.
      rewrite leq_mul2l.
      by rewrite subn_gt0 ltn_curLine orbT.
    set ld' := (BitsRepr.lsr (BitsRepr.lor ld bit) BitsRepr.one).
    set col' := (BitsRepr.lor col bit).
    set rd' := (BitsRepr.lsl (BitsRepr.lor rd bit) BitsRepr.one).
    set B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize].
    set poss' := (BitsRepr.land poss (BitsRepr.lnot bit)).
    set P' := P :\ min.
    move: (nextLine_fuel2 n fuel.+1 curLine P x)=> Hfuel2'.
    have ltn_ScurLine: curLine.+1 < BitsRepr.wordsize.
      by apply (leq_ltn_trans (n := n))=> //.
    move: (nextLine_correct n B curLine P poss ld rd col full x ltn_ScurLine HP Hqueen Hx ltn_x HminP)=> HB'cor.

    rewrite (IH2 _ _ _ _ B' (Ordinal ltn_ScurLine))=> //.
    rewrite (IH1 _ _ _ _ _ B curLine _ P')=> //.
    
    rewrite -ladd_repr.
    rewrite fromInt63_elim.
    rewrite -{1}[curCount]fromInt63_elim.
    rewrite !ladd_repr.
    rewrite [(fromInt63 curCount) + _]addnC addnA.
    move: (nextLine_splitCase n B curLine P min HminP)=> [Hu Hi].
    rewrite Hu cardsU Hi cards0 subn0 //.
    split.
    apply (fuel_gt1 Hfuel).
    apply Hfuel2'=> //.
    apply (nextLine_fuel3 n fuel.+1 curLine P x)=> //.
    apply nextLine_P=> //.
    apply (nextLine_fuel4 n curLine fuel.+1 x P)=> //.
    split.
    rewrite (nextLine_numCol n B curLine ld rd col full min P poss) //.
    apply HB'cor.
    apply (nextLine_complete n B curLine ld rd col full)=> //.
    apply (nextLine_ld n B curLine ld rd col full poss P x ltn_ScurLine)=> //.
    apply (nextLine_rd n B curLine ld rd col full poss P x ltn_ScurLine)=> //.
    apply (nextLine_col n B curLine ld rd col full poss)=> //.
    (* full *)
    apply Hqueen.
    rewrite setIdE.
    apply inter_repr=> //.
    apply HP.
    apply Hqueen.
    by apply zero_repr.
  (****************************************************)

  move=> ld col rd full B curLine Hfuel HB.
  rewrite /countNQueensAux.
  rewrite -/countNQueensAux.
  case Hend: (BitsRepr.leq col full).
  + (* col = full *)
    have HcurLine2: n = curLine.
      move: (r_col HB)=> Hcol.
      rewrite /repr_col in Hcol.
      rewrite (line_val HB).
      rewrite {1}(size_full n)=> //.
      have ->: (make_col n B) = [set x : 'I_BitsRepr.wordsize | x < n].
        apply/eqP.
        rewrite -(eq_repr col full (make_col n B) [set x : 'I_BitsRepr.wordsize | x < n ])=> //.
      apply HB.
      by trivial.
    rewrite -(nextLine_end n B curLine ld rd col full)=> //.
    by rewrite -[BitsRepr.one]fromInt63_elim fromInt63_one.
  + (* col != full *)
    set P := (~: (((make_ld n B curLine) :|: (make_rd n B curLine)) :|: (make_col n B))).
    have ltn_curLine: curLine < n.
      rewrite (eq_repr _ _ (make_col n B) [set x : 'I_BitsRepr.wordsize | x < n]) in Hend=> //.
      rewrite (line_val HB) {2}(size_full n)=> //.
      have Hprop: make_col n B \proper [set x0 : 'I_BitsRepr.wordsize | x0 < n].
        rewrite properEneq.
        have ->: make_col n B \subset [set x0 : 'I_BitsRepr.wordsize | x0 < n].
          apply/subsetP.
          rewrite /sub_mem=> i Hi.
          rewrite /make_col in_set in Hi.
          move/existsP: Hi=> [j Hj].
          rewrite in_set.
          by move: (from_correct n curLine i j B (correct HB) Hj)=> [res _].
        by rewrite Hend.
      by apply proper_card.
      apply HB.
      apply HB.
    rewrite (IH1 _ _ _ _ _ B curLine _ P)=> //.
    rewrite fromInt63_zero addn0.
    rewrite (nextLine_oneCase n B curLine ld rd col full) // => //.
    split.
    (* Hfuel1 *)
    apply (ltn_trans (n := 2 * n * (n - curLine))).
    rewrite !muln_gt0 /= gtz_n.
    rewrite subn_gt0 ltn_curLine //.
    rewrite -(ltn_add2r 1) [fuel + 1]addn1=> //.
    (* Hfuel2 *)
    apply (nextLine_fuel2' _ _ _ fuel.+1)=> //.
    (* Hfuel3 *)
    apply (nextLine_fuel3' n curLine fuel.+1)=> //.
    split.
    apply compl_repr.
    apply union_repr=> //.
    apply union_repr.
    apply HB.
    apply HB.
    apply HB.
    by rewrite /P !setCU -setIA subsetIl.
    by rewrite /P !setCU -setIAC subsetIr.
    by rewrite /P !setCU subsetIr.
Qed.
*)
Theorem queens_correct: forall n, n > 0 -> n < BitsRepr.wordsize -> countNQueens n = toInt63 #|valid_pos n|.
Proof.
  move=> n gtz_n ltn_n.
  have Hempty: forall x y, get_coord n empty_board x y = false.
    move=> x y.
    by rewrite /get_coord !tnth_mktuple.
  rewrite /countNQueens.
  move: (queens_correctInd n gtz_n ltn_n)=> [_ Hind].
  rewrite (Hind _ _ _ _ empty_board ord0)=> //.
  have ->: [set B' in valid_pos n | board_included n empty_board B'] = valid_pos n.
    rewrite -setP /eq_mem=> i.
    rewrite in_set.
    have ->: board_included n empty_board i = true.
      rewrite /board_included.
      apply/forallP=> x.
      apply/forallP=> y.
      by rewrite Hempty implyFb.
    by rewrite andbT.
  rewrite //.
  have H: forall P,
    [set i : 'I_BitsRepr.wordsize | [exists j, exists j',
               get_coord n empty_board j j' && P i j j']] = set0.
    move=> P.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    rewrite negb_exists.
    apply/forallP=> j'.
    by rewrite Hempty andbC andbF.
  have Hcol: (make_col n empty_board) = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    by rewrite Hempty.

  (* Handle ld, rd & col directly *)
  split; try (rewrite /repr_ld /repr_rd /native_repr;
              exists (zero BitsRepr.wordsize);
              split;
              [ rewrite -{1}fromNat0; exact: BitsRepr.zero_repr
              | try rewrite /make_ld /make_rd H;
                try rewrite Hcol;
                exact: spec.empty_repr]).
  by rewrite Hcol cards0.

  rewrite /is_correct.
  apply/forallP=> i.
  apply/forallP=> i'.
  rewrite Hempty.
  by apply implyFb.

  rewrite /is_complete.
  apply/forallP=> x.
  by apply/implyP=> //.

  rewrite /repr_full /native_repr.
  exists (decB (shlBn #1 n)).
  split.
  apply BitsRepr.ldec_repr.
  apply BitsRepr.lsl_repr.
  apply BitsRepr.one_repr.
  by eexists; split; first by rewrite toInt63_def; apply BitsRepr.toInt63_repr.
  apply spec.subset_repr.
  by rewrite leq_eqVlt ltn_n orbT.
Qed.

Cd "extraction".

Require Import ExtrOcamlBasic.

Separate Extraction countNQueens.
