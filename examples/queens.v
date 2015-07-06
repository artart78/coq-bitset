From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Require Import bineqs repr_op.

Fixpoint countNQueensEachPos (poss: BitsRepr.Int63)(ld: BitsRepr.Int63)(col: BitsRepr.Int63)(rd: BitsRepr.Int63)(curCount: nat)(full: BitsRepr.Int63)(fuel: nat)
  := match fuel with
     | 0 => 0
     | n'.+1 =>
       if (BitsRepr.leq (BitsRepr.land poss full) BitsRepr.zero) then
         curCount
       else (
         let bit := BitsRepr.land poss (BitsRepr.lneg poss) in
         let count := countNQueensAux (BitsRepr.lsr (BitsRepr.lor ld bit) 1) (BitsRepr.lor col bit) (BitsRepr.lsl (BitsRepr.lor rd bit) 1) full n' in
         countNQueensEachPos (BitsRepr.land poss (BitsRepr.lnot bit)) ld col rd (curCount + count) full n'
       )
     end
with countNQueensAux (ld: BitsRepr.Int63)(col: BitsRepr.Int63)(rd: BitsRepr.Int63)(full: BitsRepr.Int63)(fuel: nat)
  := match fuel with
     | 0 => 0
     | n'.+1 =>
       if (BitsRepr.leq col full) then
         1
       else (
         let poss := BitsRepr.lnot (BitsRepr.lor (BitsRepr.lor ld rd) col) in
         countNQueensEachPos poss ld col rd 0 full n'
       )
     end.

Definition countNQueens (n: nat) (fuel: nat)
  := countNQueensAux BitsRepr.zero BitsRepr.zero BitsRepr.zero (BitsRepr.ldec (BitsRepr.lsl BitsRepr.one n)) fuel.

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
      rewrite !in_set.
      rewrite ltnS leq_eqVlt.
      have ->: (i == @inord BitsRepr.wordsize.-1 n) = (nat_of_ord i == n).
        case H: (nat_of_ord i == n).
        + (* i == n *)
          move/eqP: H=> H.
          apply/eqP.
          apply ord_inj.
          by rewrite inordK.
        + (* i <> n *)
          apply negbTE.
          apply/negP.
          move=> Habs.
          have Habs': nat_of_ord i == n.
            move/eqP: Habs=> Habs.
            apply/eqP.
            by rewrite Habs inordK.
          by rewrite Habs' in H.
        rewrite //.
    rewrite cardsU1.
    rewrite -IHn=> //.
    have ->: (@inord 62 n \notin [set x : 'I_BitsRepr.wordsize | x < n]).
      rewrite in_set inordK => //.
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

Lemma from_included: forall n B i j j', board_included n B i -> get_coord n B j j' -> get_coord n i j j'.
  move=> n B i j j' Hincl Hjj'.
  rewrite /board_included in Hincl.
  move/forallP: Hincl=> Hincl.
  move: (Hincl j)=> /forallP Hinclj.
  move: (Hinclj j')=> Hincljj'.
  by rewrite Hjj' /= in Hincljj'.
Qed.

Set Printing Projections.

Lemma queensEachPos_correct (n: nat) : n < BitsRepr.wordsize -> forall fuel,
  forall poss ld col rd full B (curLine: 'I_BitsRepr.wordsize) curCount (P: {set 'I_BitsRepr.wordsize}),
    curLine < n ->
    fuel > 0 ->
    (forall x : 'I_BitsRepr.wordsize, x < n /\ x \in P -> fuel >= (2 * n * (n - curLine) - [arg min_(k < x in P) k]).+1) ->
    @repr_queen n B curLine ld rd col full ->
    @repr_poss n B curLine P poss ->
      countNQueensEachPos poss ld col rd curCount full fuel =
        #|[set B' in (valid_pos n) | board_included n B B' && board_possible n P B' curLine]| + curCount
with queensAux_correct (n: nat) : n < BitsRepr.wordsize -> forall fuel,
  forall ld col rd full B (curLine: 'I_BitsRepr.wordsize),
    fuel >= (2 * n * (n - curLine) + 1).+1 ->
    @repr_queen n B curLine ld rd col full ->
      countNQueensAux ld col rd full fuel =
        #|[set B' in (valid_pos n) | board_included n B B']|.
Proof.
  move=> ltn_n fuel poss ld col rd full B curLine curCount P ltn_curLine Hfuel1 Hfuel2 Hqueen HP.
  have Hfuel': fuel = fuel.-1.+1 by rewrite prednK.
  rewrite Hfuel'.
  rewrite /countNQueensEachPos.
  rewrite -/countNQueensAux.
  rewrite -/countNQueensEachPos.
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
      rewrite in_set in_set0.
      rewrite /board_possible.
      rewrite /valid_pos /is_complete.
      rewrite in_set.
      apply/andP.
      move=> [/andP[/forallP Hcompl Hcor] /andP[_ /forallP Hposs]].
      move: (Hcompl curLine)=> Honeset.
      rewrite ltn_curLine implyTb in Honeset.
      move/existsP: Honeset=>[i /eqP Hi].
      move: (Hposs i)=> Hpossi.
      rewrite Hi in Hpossi.
      rewrite implyTb in Hpossi.
      move: (H1 i Hpossi)=> Habsi.
      rewrite /is_correct in Hcor.
      move/forallP: Hcor=>Hcor.
      move: (Hcor i)=> /forallP Hcori.
      move: (Hcori curLine)=> /implyP HcoricurLine.
      move: (HcoricurLine Hi)=> /andP [/andP [Habs2 _] _].
      rewrite ltnNge in Habs2.
      by rewrite Habsi // in Habs2.
    by rewrite cards0 add0n.
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
    set ld' := (BitsRepr.lsr (BitsRepr.lor ld bit) 1).
    set col' := (BitsRepr.lor col bit).
    set rd' := (BitsRepr.lsl (BitsRepr.lor rd bit) 1).
    set B' := [tuple [tuple (if ((x == min) && (y == curLine)) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize].
    set poss' := (BitsRepr.land poss (BitsRepr.lnot bit)).
    set P' := P :\ min.
    have ltn_ScurLine: curLine.+1 < BitsRepr.wordsize.
      by apply (leq_ltn_trans (n := n))=> //.
    have HB'cor: is_correct (@Ordinal BitsRepr.wordsize curLine.+1 ltn_ScurLine) n B'.
    (* is_correct B' *)
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
      move: (from_correct n curLine j j' B (correct Hqueen) Hjj'3)=> [_ [Hltn _]].
      by rewrite neq_ltn Hltn orbT.
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
      by move: (from_correct n curLine a b B (correct Hqueen) Hab')=> [ltn_a _].
      move: (from_correct n curLine a b B (correct Hqueen) Hab')=> [_ [ltn_b _]].
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
        have ->: (min == a) = (a == min) by exact: eq_sym.
        have ->: (curLine == b) = (b == curLine) by exact: eq_sym.
        rewrite Hmin /= Hab.
        have ->: ((min + b != a + curLine) = (a + curLine != min + b)) by rewrite eq_sym.
        have ->: ((a + b != min + curLine) = (min + curLine != a + b)) by rewrite eq_sym.
        move=> Hcorr.
        by apply Hcorr.
      - (* j <> min || j' <> curLine *)
        have Hjj'3: get_coord n B j j'.
          by rewrite /get_coord /B' !tnth_mktuple Hmin' in Hjj'2.
        move: (from_correct n curLine a b B (correct Hqueen) Hab')=> [_ [_ Hcorr]].
        move: (Hcorr j j')=> Hcorr1.
        by rewrite Hjj' Hjj'3 /= in Hcorr1.
    rewrite (queensAux_correct n ltn_n _ _ _ _ _ B' (Ordinal ltn_ScurLine))=> //.
    rewrite (queensEachPos_correct n ltn_n _ _ _ _ _ _ B curLine _ P')=> //.
    rewrite [curCount + _]addnC addnA.
    set setA := [set B'0 in valid_pos n | board_included n B B'0 & board_possible n P' B'0 curLine].
    set setB := [set B'0 in valid_pos n | board_included n B' B'0].
    set setC := [set B'0 in valid_pos n | board_included n B B'0 & board_possible n P B'0 curLine].
    have ->: setC = setA :|: setB.
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
              move/forallP: HiP=>HiP.
              move: (HiP x')=> /implyP HxP.
              have Hx': x' = min.
                apply/eqP.
                rewrite -in_set1.
                have ->: [set min] = P :\: P'.
                rewrite setDDr setDv set0U.
                symmetry.
                apply /setIidPr.
                by rewrite sub1set.
              rewrite in_setD Hx2 (HxP Hx1) //.
              move/andP: Hmin=>[/eqP Hmin1 /eqP Hmin2].
              by rewrite Hmin1 Hmin2 -Hx' Hx1.
            + (* x0 == min && y0 == curLine is false *)
              rewrite /B' /get_coord in HinB'.
              rewrite !tnth_mktuple in HinB'.
              rewrite Hmin in HinB'.
              rewrite /board_included in HBi.
              move/forallP: HBi=>HBi.
              move: (HBi x0)=> HBix.
              move/forallP: HBix=>HBix.
              move: (HBix y0)=> HBixy.
              by move/implyP: HBixy ->=> //.
          + (* board_possible n P i curLine = false *)
            case HiP': (board_possible n P' i curLine).
            + (* board_possible n P' i curLine = true *)
              rewrite orbC orbT.
              have: board_possible n P i curLine = true.
                rewrite /board_possible.
                apply/forallP.
                move=> y.
                apply/implyP=> Hy.
                rewrite /board_possible in HiP'.
                move/forallP: HiP'=>HiP'.
                move: (HiP' y)=> /implyP HiP'y.
                rewrite in_setD in HiP'y.
                move: (HiP'y Hy)=> /andP [_ HyP] //.
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
                rewrite {1}/get_coord /B' !tnth_mktuple.
                have ->: (min == min) by trivial.
                have ->: (curLine == curLine) by trivial.
                rewrite andbT andbC andbT.
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
                  rewrite /is_correct in Hicorr.
                  move/forallP: Hicorr=> Hicorr.
                  move: (Hicorr j)=> /forallP Hicorr1.
                  move: (Hicorr1 curLine)=> Hicorr2.
                  rewrite Hj implyTb in Hicorr2.
                  move: Hicorr2 => /andP [_ /forallP Hicorr3].
                  move: (Hicorr3 min)=> /forallP Hicorr4.
                  move: (Hicorr4 curLine)=> Hicorr5.
                  rewrite Hmin implyTb in Hicorr5.
                  rewrite Habs andbC andbF /= in Hicorr5.
                  move: Hicorr5=> /andP [/andP [Habs' _] _].
                  by move/eqP: Habs'.
              by rewrite //.
        by rewrite //.
      by rewrite //.
      by rewrite andbF andbC andbF andbC andbF.
    rewrite cardsU.
    have ->: setA :&: setB = set0.
      rewrite -setP /eq_mem=> i.
      rewrite in_setI !in_set.
      case Hinc: (board_included n B' i) setB=> setB.
      + (* B' included in i *)
        case Hpos: (board_possible n P' i curLine).
        - (* (x, curLine) in i => x in P' *)
          exfalso.
          have Hmin: get_coord n i min curLine.
            rewrite /board_included in Hinc.
            move/forallP: Hinc=> Hinc.
            move: (Hinc min)=> /forallP Hinc2.
            move: (Hinc2 curLine)=> Hinc3.
            have Hmin: get_coord n B' min curLine.
              rewrite /B' /get_coord !tnth_mktuple.
              have ->: (min == min) by trivial.
              by have ->: (curLine == curLine) by trivial.
            by rewrite Hmin implyTb in Hinc3.
          rewrite /board_possible in Hpos.
          move/forallP: Hpos=> Hpos.
          move: (Hpos min)=> Hpos2.
          rewrite Hmin implyTb in_setD in Hpos2.
          move/andP: Hpos2=> [Habs _].
          rewrite in_set1 in Habs.
          by move/eqP: Habs.
        - (* board_possible n P' i curLine = false *)
          by rewrite andbF andbF andbC andbF.
      + (* B' not included in i *)
        by rewrite !andbF.
    rewrite cards0 subn0 //.
    (* Hfuel1 *)
    rewrite (leq_ltn_trans (n := 2 * n * (n - curLine) - [arg min_(k < x in P') k])) //.
    admit. (* Thanks to Hfuel2 below *)
    (* Hfuel2 *)
    move=> x' [ltn_x' Hx'].
    admit. (* 2 * n * (n - curLine) - [arg min_(k < x' in P') k] < fuel.-1 because the minimum in P' is > to the minimum in P *)
    split.
    (* P' *)
    rewrite /P'.
    rewrite setDE.
    apply inter_repr=> //.
    apply HP.
    apply compl_repr.
    apply keep_min_repr=> //.
    apply HP.
    (* TODO: factorize *)
    (* P' \subset (~: make_ld n B curLine) *)
    rewrite /P'.
    apply (subset_trans (B := pred_of_set P))=> //.
    by rewrite subD1set.
    by apply HP.
    (* P' \subset (~: make_rd n B curLine) *)
    rewrite /P'.
    apply (subset_trans (B := pred_of_set P))=> //.
    by rewrite subD1set.
    by apply HP.
    (* P' \subset (~: make_col n B) *)
    rewrite /P'.
    apply (subset_trans (B := pred_of_set P))=> //.
    by rewrite subD1set.
    by apply HP.
    (* n * (n + 1 - curLine.+1) <= fuel.-1 *)
    rewrite /=.
    rewrite -(leq_add2r 1) !addn1 -Hfuel'.
    apply (leq_ltn_trans (n := 2 * n * (n - curLine) - [arg min_(k < x in P) k])).
    admit. (* Thanks to [arg min_(k < x in P) k] < 2n - 1 *)
    apply (Hfuel2 x).
    by rewrite ltn_x Hx.
    split.
    (* curLine.+1 = #|make_col n B'| *)
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
      by rewrite cards0 subn0 -(line_val Hqueen) cards1 addn1.
    apply HB'cor.
    (* is_complete curLine.+1 B' *)
    rewrite /is_complete.
    apply/forallP=> j.
    apply/implyP=> ltn_j.
    case Hj: (j == curLine).
    + (* j == curLine *)
      apply/existsP.
      exists min.
      rewrite /get_coord !tnth_mktuple Hj.
      by have ->: min == min by trivial.
    + (* j <> curLine *)
      have Hj': j < curLine.
        rewrite ltn_neqAle.
        apply negbT in Hj.
        rewrite Hj andbC andbT.
        by rewrite -(leq_add2r 1) !addn1.
      move: (complete Hqueen)=> HBcompl.
      rewrite /is_complete in HBcompl.
      move/forallP: HBcompl=> HBcompl.
      move: (HBcompl j)=> HBcomplj.
      rewrite Hj' /= in HBcomplj.
      move/existsP: HBcomplj=> [k' Hk'].
      apply/existsP.
      exists k'.
      rewrite /get_coord /B'.
      by rewrite !tnth_mktuple Hj andbF.
    (* ld' *)
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
          move/forallP: HB'cor=>HB'cor.
          move: (HB'cor j)=> HB'corj.
          move/forallP: HB'corj=>HB'corj.
          move: (HB'corj j')=> /implyP HB'corjj'.
          move: (HB'corjj' Hjj')=> /andP [/andP [Hj Hj'] _].
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
        rewrite //=.
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
        rewrite /B' /get_coord !tnth_mktuple.
        have ->: min == min by trivial.
        have ->: curLine == curLine by trivial.
        move/eqP: Hi ->.
        by rewrite /=.
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
    apply Hqueen.
    apply keep_min_repr=> //.
    apply HP.
    (* rd' *)
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
        have ->: i + j' != j + curLine.+1.
          rewrite neq_ltn.
          have ->: i + j' < j + curLine.+1.
            have ->: i = ord0.
              apply negbT in Hi.
              rewrite -eqn0Ngt in Hi.
              move/eqP: Hi=> Hi.
              apply ord_inj.
              by rewrite Hi.
            have ->: ord0 (n' := BitsRepr.wordsize.-1) + j' = j' by trivial.
            rewrite ltn_addl //.
            move/forallP: HB'cor=>HB'cor.
            move: (HB'cor j)=> /forallP HB'corj.
            move: (HB'corj j')=> /implyP HB'corjj'.
            move: (HB'corjj' Hjj')=> /andP [/andP [Hj Hj'] _].
            apply Hj'.
          by rewrite /=.
      rewrite //.
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
    apply Hqueen.
    apply keep_min_repr=> //.
    by apply HP.
    (* col' *)
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
  apply Hqueen.
  apply keep_min_repr=> //.
  apply HP.
  apply Hqueen.
  rewrite setIdE.
  apply inter_repr=> //.
  apply HP.
  apply Hqueen.
  by apply zero_repr.
  (****************************************************)

  move=> ltn_n fuel ld col rd full B curLine Hfuel HB.
  have Hfuel': fuel = fuel.-1.+1.
    by rewrite prednK //; apply (leq_ltn_trans (n := 2 * n * (n - curLine) + 1)).
  rewrite Hfuel'.
  rewrite /countNQueensAux.
  rewrite -/countNQueensEachPos.
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
            rewrite /board_included in H3.
            move/forallP: H3=> H3.
            move: (H3 x)=> H3x.
            move/forallP: H3x=> H3x.
            move: (H3x y)=> /implyP H3xy.
            rewrite /get_coord in H3xy.
            by rewrite H3xy.
          - (* tnth (tnth B x) y = false *)
            case Hy: (y < curLine).
            + (* y < curLine *)
              move: (complete HB)=> HBcompl.
              rewrite /is_complete in HBcompl.
              move/forallP: HBcompl=> HBcompl.
              move: (HBcompl y)=> HBcompl2.
              rewrite Hy /= in HBcompl2.
              move/existsP: HBcompl2=> [k' /eqP Hk'].
              rewrite -HcurLine2 in Hk'.
              have Hk'1: get_coord n B' k' y.
                rewrite /board_included in H3.
                move/forallP: H3=> H3.
                move: (H3 k')=> /forallP H3'.
                move: (H3' y)=> H3''.
                by rewrite Hk' /= in H3''.
              rewrite /is_correct in H2.
              move/forallP: H2=>H2'.
              move: (H2' k')=> /forallP H2''.
              move: (H2'' y)=> H2'''.
              rewrite Hk'1 /= in H2'''.
              move: H2'''=> /andP [_ /forallP Hcorr'].
              move: (Hcorr' x)=> /forallP Hcorr''.
              move: (Hcorr'' y)=> Hcorr'''.
              have Htrivial: y == y by trivial.
              rewrite Htrivial /= andbT andbF andbC in Hcorr'''.
              case Hk'x: (k' != x).
              + (* k' != x *)
                rewrite Hk'x /= andbF /get_coord implybF in Hcorr'''.
                by apply negbTE.
              + (* k' == x *)
                apply negbT in Hk'x.
                move/negPn: Hk'x=> /eqP Hk'x.
                rewrite Hk'x in Hk'.
                rewrite /get_coord in Hk'.
                by rewrite Hxy in Hk'.
            + (* y >= curLine *)
              rewrite /is_correct in H2.
              move/forallP: H2=>H2.
              move: (H2 x)=> /forallP H2'.
              move: (H2' y)=> H2''.
              rewrite {3}HcurLine2 Hy andbF andbC andbF implybF /get_coord in H2''.
              by apply negbTE.
        rewrite Habs in HB'.
        move/eqP: HB'=>HB'.
        by rewrite //.
    by rewrite cards1.
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
    rewrite (queensEachPos_correct n ltn_n _ _ _ _ _ _ B curLine _ P)=> //.
    rewrite addn0.
    have ->: [set B' in valid_pos n | board_included n B B' & board_possible n P B' curLine]
           = [set B' in valid_pos n | board_included n B B'].
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
          have Hx: x == x by trivial.
          rewrite Hx /= in Hicorr2'.
          rewrite (from_included n B i x j HBi Hj) /= in Hicorr2'.
          have Hj2': (curLine == j) = false.
            apply negbTE.
            by rewrite neq_ltn Hj2 orbT.
          by rewrite Hj2' /= in Hicorr2'.
        by rewrite /=.
      + (* ~~ (is_complete n i && is_correct n n i && board_included n B i ) *)
        by rewrite andbC andbF.
    rewrite //.
    (* Hfuel1 *)
    apply (ltn_trans (n := 2 * n * (n - curLine))).
    admit. (* Easy thanks to ltn_curLine *)
    rewrite -(ltn_add2r 1) [2 * n * (n - curLine) + 1]addn1 [fuel.-1 + 1]addn1 -Hfuel' -addn1=> //.
    (* Hfuel2 *)
    move=> x [ltn_x Hx].
    admit.
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
Admitted.

Theorem queens_correct: forall n, n > 0 -> n < BitsRepr.wordsize -> countNQueens n (2 * n * n + 2) = #|valid_pos n|.
Proof.
  move=> n gtz_n ltn_n.
  have Hempty: forall x y, get_coord n empty_board x y = false.
    move=> x y.
    by rewrite /get_coord !tnth_mktuple.
  rewrite /countNQueens.
  rewrite (queensAux_correct n ltn_n _ _ _ _ _ empty_board ord0)=> //.
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
  rewrite subn0 ltn_add2l //.
  split.
  rewrite /make_col.
  have ->: [set i | [exists i', get_coord n empty_board i i']] = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    apply negbTE.
    rewrite negb_exists.
    apply/forallP =>x.
    by rewrite Hempty.
  by rewrite cards0.

  rewrite /is_correct.
  apply/forallP=> i.
  apply/forallP=> i'.
  rewrite Hempty.
  apply implyFb.
  rewrite /is_complete.
  apply/forallP=> x.
  apply/implyP=> //.
  (* TODO: factorize ld, rd and col *)
  (* ld *)
  rewrite /repr_ld /native_repr.
  exists (zero BitsRepr.wordsize).
  rewrite -{1}fromNat0.
  split.
  exact: BitsRepr.zero_repr.
  have ->: (make_ld n empty_board 0) = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: [exists j, exists j', get_coord n empty_board j j' && (i + 0 == j + j')] = false.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    rewrite negb_exists.
    apply/forallP=> j'.
    rewrite Hempty andbC andbF //.
    rewrite //.
  apply spec.empty_repr.
  (* rd *)
  rewrite /repr_rd /native_repr.
  exists (zero BitsRepr.wordsize).
  rewrite -{1}fromNat0.
  split.
  exact: BitsRepr.zero_repr.
  have ->: (make_rd n empty_board 0) = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    rewrite negb_exists.
    apply/forallP=> j'.
    by rewrite Hempty andbC andbF.
  apply spec.empty_repr.
  (* col *)
  rewrite /repr_col /native_repr.
  exists (zero BitsRepr.wordsize).
  rewrite -{1}fromNat0.
  split.
  exact: BitsRepr.zero_repr.
  have ->: (make_col n empty_board) = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    by rewrite Hempty.
  apply spec.empty_repr.
  rewrite /repr_full.
  rewrite /native_repr.
  exists (decB (shlBn #1 n)).
  split.
  apply BitsRepr.ldec_repr.
  apply BitsRepr.lsl_repr.
  apply BitsRepr.one_repr.
  apply spec.subset_repr.
  by rewrite leq_eqVlt ltn_n orbT.
Qed.

Cd "extraction".

Separate Extraction countNQueens.
