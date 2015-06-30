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
  [forall k : 'I_BitsRepr.wordsize, (0 <= k < n) ==>
    [exists k', get_coord n B k' k == true]].

Definition is_correct cur n B :=
  [forall i : 'I_BitsRepr.wordsize, forall i' : 'I_BitsRepr.wordsize,
   (get_coord n B i i') ==> (i < n) && (i' < cur)
   && [forall j : 'I_BitsRepr.wordsize, forall j' : 'I_BitsRepr.wordsize, (get_coord n B j j') ==>
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
  := native_repr full [set x : 'I_BitsRepr.wordsize | 0 <= x < n].

Definition board_included n B B' := [forall x, forall y, get_coord n B x y ==> get_coord n B' x y].

Definition empty_board := [tuple [tuple false | i < BitsRepr.wordsize] | i < BitsRepr.wordsize].

Definition board_possible n (P: {set ordinal_finType BitsRepr.wordsize}) B' i' := [forall i, get_coord n B' i i' ==> (i \in P)].

Set Printing Implicit.

(* Note: i' is the number of columns (cardinal of make_col), it should probably be replaced *)
(* Note: we want i' < n in the hypothesises or easily deducible *)
(* Note: there's a missing hypothesis about 'poss': that all of these positions still make it correct *)
(* Note: it should be added that, if i is in 'poss', it is not in 'col' *)
(* Note: the hypothesis "everything below i' is empty" would also be handy *)
Lemma queensEachPos_correct (n: nat) : n <= BitsRepr.wordsize -> exists f, forall fuel, fuel >= f ->
  forall poss ld col rd full B (i': 'I_BitsRepr.wordsize),
    forall curCount, is_correct i' n B -> is_complete i' B ->
      (repr_ld n B i' ld) -> (repr_rd n B i' rd) -> (repr_col n B col) -> (repr_full n full) ->
      forall P, (native_repr poss P) ->
      countNQueensEachPos poss ld col rd curCount full fuel =
        #|[set B' in (valid_pos n) | board_included n B B' && board_possible n P B' i']| + curCount
with queensAux_correct (n: nat) : n <= BitsRepr.wordsize -> exists f, forall fuel, fuel >= f ->
  forall ld col rd full B (i': 'I_BitsRepr.wordsize), is_correct i' n B -> is_complete i' B ->
    (repr_ld n B i' ld) -> (repr_rd n B i' rd) -> (repr_col n B col) -> (repr_full n full) ->
      countNQueensAux ld col rd full fuel =
        #|[set B' in (valid_pos n) | board_included n B B']|.
Proof.
  move=> ltn_n.
  move: (queensAux_correct n ltn_n)=> [f H].
  move: (queensEachPos_correct n ltn_n)=> [f' H'].
  exists ((maxn f f').+1).
  move=> fuel Hfuel poss ld col rd full B i' curCount HBcor HBcompl Hld Hrd Hcol Hfull P HP.
  have Hfuel': fuel = fuel.-1.+1.
    by rewrite (ltn_predK (m := maxn f f')).
  rewrite Hfuel'.
  rewrite /countNQueensEachPos.
  rewrite -/countNQueensAux.
  rewrite -/countNQueensEachPos.
  case: (BitsRepr.leq (BitsRepr.land poss full) BitsRepr.zero).
  + (* (poss & full) == 0 *)
    have H1: forall x : 'I_BitsRepr.wordsize, x \in P -> x >= n by admit. (* Representation... *)
    have ->: [set B' in valid_pos n | board_included n B B' & board_possible n P B' i'] = set0.
      rewrite -setP /eq_mem=> B0.
      rewrite in_set in_set0.
      rewrite /board_possible.
      rewrite /valid_pos /is_complete.
      rewrite in_set.
      apply/andP.
      move=> [/andP[/forallP Hcompl Hcor] /andP[_ /forallP Hposs]].
      have ltn_i': 0 <= i' < n by admit. (* This should always be true, by hypothesis *)
      move: (Hcompl i')=> Honeset.
      rewrite ltn_i' implyTb in Honeset.
      move/existsP: Honeset=>[i /eqP Hi].
      move: (Hposs i)=> Hpossi.
      rewrite Hi in Hpossi.
      rewrite implyTb in Hpossi.
      move: (H1 i Hpossi)=> Habsi.
      rewrite /is_correct in Hcor.
      move/forallP: Hcor=>Hcor.
      move: (Hcor i)=> /forallP Hcori.
      move: (Hcori i')=> /implyP Hcorii'.
      move: (Hcorii' Hi)=> /andP [/andP [Habs2 _] _].
      rewrite ltnNge in Habs2.
      by rewrite Habsi // in Habs2.
    by rewrite cards0 add0n.
  + (* (poss & full) != 0 *)
    set bit := (BitsRepr.land poss (BitsRepr.lneg poss)).
    have: exists x : 'I_BitsRepr.wordsize, x < n /\ x \in P by admit. (* Representation... *)
    move=> [x [ltn_x Hx]].
    set min := [arg min_(k < x in P) k].
    set ld' := (BitsRepr.lsr (BitsRepr.lor ld bit) 1).
    set col' := (BitsRepr.lor col bit).
    set rd' := (BitsRepr.lsl (BitsRepr.lor rd bit) 1).
    set B' := [tuple [tuple (if ((x == min) && (y == i')) then true else get_coord n B x y) | y < BitsRepr.wordsize] | x < BitsRepr.wordsize].
    set poss' := (BitsRepr.land poss (BitsRepr.lnot bit)).
    set P' := P :\ min.
    have ltn_i': i'.+1 < BitsRepr.wordsize by admit. (* Because i'.+1 < n, because i' is the number of occupied columns in 'col' and col is not full, because poss in not full *)
    rewrite (H _ _ _ _ _ _ B' (Ordinal ltn_i'))=> //.
    rewrite (H' _ _ _ _ _ _ _ B i' _ _ _ _ _ _ _ P')=> //.
    rewrite [curCount + _]addnC addnA.
    set setA := [set B'0 in valid_pos n | board_included n B B'0 & board_possible n P' B'0 i'].
    set setB := [set B'0 in valid_pos n | board_included n B' B'0].
    set setC := [set B'0 in valid_pos n | board_included n B B'0 & board_possible n P B'0 i'].
    have ->: setC = setA :|: setB.
      rewrite -setP /eq_mem=> i.
      rewrite in_setU !in_set.
      rewrite -Bool.andb_orb_distrib_r.
      case Hicorr: (is_correct n n i).
      have ->: board_included n B i && board_possible n P i i'
             = board_included n B i && board_possible n P' i i' || board_included n B' i.
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
        have ->: board_possible n P i i' = board_possible n P' i i' || board_included n B' i.
          case HiP: (board_possible n P i i').
          + (* board_possible n P i i' = true *)
            case HiP': (board_possible n P' i i')=> //=.
            rewrite /board_included.
            symmetry.
            apply/forallP=> x0.
            apply/forallP=> y0.
            apply/implyP=> HinB'.
            case Hmin: ((x0 == min) && (y0 == i')).
            + (* x0 == min && y0 == i' is true *)
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
                rewrite sub1set.
                rewrite /min /arg_min.
                case: pickP=> y //=.
                by move/andP => [H1 _].
              rewrite in_setD Hx2 (HxP Hx1) //.
              move/andP: Hmin=>[/eqP Hmin1 /eqP Hmin2].
              by rewrite Hmin1 Hmin2 -Hx' Hx1.
            + (* x0 == min && y0 == i' is false *)
              rewrite /B' /get_coord in HinB'.
              rewrite !tnth_mktuple in HinB'.
              rewrite Hmin in HinB'.
              rewrite /board_included in HBi.
              move/forallP: HBi=>HBi.
              move: (HBi x0)=> HBix.
              move/forallP: HBix=>HBix.
              move: (HBix y0)=> HBixy.
              by move/implyP: HBixy ->=> //.
          + (* board_possible n P i i' = false *)
            case HiP': (board_possible n P' i i').
            + (* board_possible n P' i i' = true *)
              rewrite orbC orbT.
              have: board_possible n P i i' = true.
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
            + (* board_possible n P' i i' = false *)
              have: board_included n B' i = false.
                rewrite /board_included.
                apply/forallP/forallP.
                rewrite negb_forall.
                apply/existsP.
                exists min.
                rewrite negb_forall.
                apply/existsP.
                exists i'.
                rewrite negb_imply.
                rewrite {1}/get_coord /B' !tnth_mktuple.
                have ->: (min == min) by trivial.
                have ->: (i' == i') by trivial.
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
                  have Habs': min \in P.
                    rewrite /min /arg_min.
                    case: pickP=> y //=.
                    by move/andP => [H1 _].
                  by rewrite Habs' in HjP.
                - (* j <> min *)
                  apply/negP=> Hmin.
                  rewrite /is_correct in Hicorr.
                  move/forallP: Hicorr=> Hicorr.
                  move: (Hicorr j)=> /forallP Hicorr1.
                  move: (Hicorr1 i')=> Hicorr2.
                  rewrite Hj implyTb in Hicorr2.
                  move: Hicorr2 => /andP [_ /forallP Hicorr3].
                  move: (Hicorr3 min)=> /forallP Hicorr4.
                  move: (Hicorr4 i')=> Hicorr5.
                  rewrite Hmin implyTb in Hicorr5.
                  move: Hicorr5=> /andP [/andP [/andP[ _ Habs'] _] _].
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
        case Hpos: (board_possible n P' i i').
        - (* (x, i') in i => x in P' *)
          exfalso.
          have Hmin: get_coord n i min i'.
            rewrite /board_included in Hinc.
            move/forallP: Hinc=> Hinc.
            move: (Hinc min)=> /forallP Hinc2.
            move: (Hinc2 i')=> Hinc3.
            have Hmin: get_coord n B' min i'.
              rewrite /B' /get_coord !tnth_mktuple.
              have ->: (min == min) by trivial.
              by have ->: (i' == i') by trivial.
            by rewrite Hmin implyTb in Hinc3.
          rewrite /board_possible in Hpos.
          move/forallP: Hpos=> Hpos.
          move: (Hpos min)=> Hpos2.
          rewrite Hmin implyTb in_setD in Hpos2.
          move/andP: Hpos2=> [Habs _].
          rewrite in_set1 in Habs.
          by move/eqP: Habs.
        - (* board_possible n P' i i' = false *)
          by rewrite andbF andbF andbC andbF.
      + (* B' not included in i *)
        by rewrite !andbF.
    rewrite cards0 subn0 //.
    rewrite -(leq_add2r 1) !addn1 -Hfuel'.
    rewrite gtn_max in Hfuel.
    case: (f < fuel) in Hfuel=> //.
    (* P' *)
    rewrite /P'.
    rewrite setDE.
    apply inter_repr=> //.
    apply compl_repr.
    apply keep_min_repr=> //.
    (* f <= fuel.-1 *)
    rewrite -(leq_add2r 1) !addn1 -Hfuel'.
    rewrite gtn_max in Hfuel.
    case: (f' < fuel) in Hfuel=> //.
    rewrite andbT in Hfuel=> //.
    rewrite andbF in Hfuel=> //.
    (* is_correct B' *)
    admit. (* B is correct & the 3 conditions are respected thanks to the spec of 'poss' *)
    (* is_complete i'.+1 B' *)
    admit. (* Easy: there is one for each line thanks to B + the added one *)
    (* ld' *)
    rewrite /repr_ld.
    have ->: (make_ld n B' (Ordinal ltn_i')) = [set i : 'I_BitsRepr.wordsize | (i < BitsRepr.wordsize.-1) && (inord i.+1 \in (make_ld n B' i'))].
      rewrite /make_ld -setP /eq_mem=> i.
      rewrite !in_set.
      have Habs: i.+1 >= n -> [exists j, exists j', get_coord n B' j j' && (i + i'.+1 == j + j')] = false.
        move=> leq_n.
        apply negbTE.
        rewrite negb_exists.
        apply/forallP=> j.
        rewrite negb_exists.
        apply/forallP=> j'.
        rewrite negb_and.
        rewrite neq_ltn.
        case Hjj': (get_coord n B' j j')=> //.
        have ->: j + j' < i + i'.+1.
          rewrite -[i'.+1]add1n addnA addn1.
          have HB'cor: is_correct (Ordinal ltn_i') n B' by admit.
          move/forallP: HB'cor=>HB'cor.
          move: (HB'cor j)=> HB'corj.
          move/forallP: HB'corj=>HB'corj.
          move: (HB'corj j')=> /implyP HB'corjj'.
          move: (HB'corjj' Hjj')=> /andP [/andP [Hj Hj'] _].
          apply (leq_trans (n := n + i')).
          apply (leq_ltn_trans (n := j + i')).
          rewrite leq_add2l=> //.
          rewrite ltn_add2r=> //.
          rewrite leq_add2r=> //.
        by rewrite orbT orbT.
      case ltn'_i: (i < BitsRepr.wordsize .-1).
      + (* i < BitsRepr.wordsize .-1 *)
        rewrite inordK.
        have ->: i + i'.+1 = i.+1 + i'.
          by rewrite -add1n addnA addn1 //.
        rewrite //=.
        rewrite -[i.+1]addn1 -[63]addn1 ltn_add2r.
        by apply ltn'_i.
      + (* i >= BitsRepr.wordsize .-1 *)
        have Hi: i.+1 >= n.
          apply (leq_trans (n := BitsRepr.wordsize))=> //.
          rewrite -(leq_add2r 1) !addn1 /= in ltn'_i.
          rewrite leqNgt.
          rewrite ltn'_i //.
        by rewrite (Habs Hi).
    admit. (* Representation of lsr *)
    (* rd' *)
    rewrite /repr_rd.
    have ->: (make_rd n B' (Ordinal ltn_i')) = [set i : 'I_BitsRepr.wordsize | ((i > 0) && (inord i.-1 \in (make_rd n B' i')))].
      rewrite /make_rd -setP /eq_mem=> i.
      rewrite !in_set.
      case Hi: (i > 0)=> /=.
      + (* i > 0 *)
        rewrite inordK.
        have Heq: forall j j', (i.-1 + j' == j + i') = (i + j' == j + i'.+1).
          move=> j j'.
          rewrite -(eqn_add2r 1).
          rewrite addnC addnA -subn1 subnKC=> //.
          by rewrite -addnA addn1.
        case Hex: [exists j, exists j', get_coord n B' j j' && (i + j' == j + i'.+1)].
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
        have ->: i + j' != j + i'.+1.
          rewrite neq_ltn.
          have ->: i + j' < j + i'.+1.
            have ->: i = ord0.
              apply negbT in Hi.
              rewrite -eqn0Ngt in Hi.
              move/eqP: Hi=> Hi.
              apply ord_inj.
              by rewrite Hi.
            have ->: ord0 (n' := BitsRepr.wordsize.-1) + j' = j' by trivial.
            rewrite ltn_addl //.
            have HB'cor: is_correct (Ordinal ltn_i') n B' by admit.
            move/forallP: HB'cor=>HB'cor.
            move: (HB'cor j)=> /forallP HB'corj.
            move: (HB'corj j')=> /implyP HB'corjj'.
            move: (HB'corjj' Hjj')=> /andP [/andP [Hj Hj'] _].
            apply Hj'.
          by rewrite /=.
      rewrite //.
    admit. (* Representation of lsl *)
    (* col' *)
    rewrite /repr_col.
    have ->: make_col n B' = (make_col n B) :|: [set min].
      rewrite /make_col -setP /eq_mem=> i.
      rewrite in_setU !in_set.
      case Hi: (i == min).
      + (* i == min *)
        rewrite orbT.
        apply/existsP.
        exists i'.
        rewrite /B' /get_coord !tnth_mktuple Hi /=.
        by have ->: i' == i' by trivial.
      + (* i <> min *)
        rewrite orbF.
        rewrite /B' {1}/get_coord !tnth_mktuple Hi /=.
        case Hi'0: [exists i'0, get_coord n B i i'0].
        + (* [exists i'0, get_coord n B i i'0] *)
          move/existsP: Hi'0=> [y Hy].
          apply/existsP.
          exists y.
          by rewrite tnth_mktuple.
        + (* ~~ [exists i'0, get_coord n B i i'0] *)
          apply negbT in Hi'0.
          rewrite negb_exists in Hi'0.
          move/forallP: Hi'0=>Hi'0.
          apply negbTE.
          rewrite negb_exists.
          apply/forallP=> y.
          rewrite tnth_mktuple.
          by apply (Hi'0 y).
    apply union_repr=> //.
    apply keep_min_repr=> //.

  (****************************************************)

  move=> ltn_n.
  move: (queensEachPos_correct n ltn_n)=> [f H].
  exists (f.+1).
  move=> fuel Hfuel ld col rd full B i' HBcorr HBcompl Hld Hrd Hcol Hfull.
  have Hfuel': fuel = fuel.-1.+1.
    by rewrite (ltn_predK (m := f)).
  rewrite Hfuel'.
  rewrite /countNQueensAux.
  rewrite -/countNQueensEachPos.
  case Hend: (BitsRepr.leq col full).
  + (* col = full *)
    have Hi': n = i' by admit. (* Immediate if i' = #|make_col| *)
    have ->: [set B' in valid_pos n | board_included n B B'] = [set B].
      rewrite -setP /eq_mem=> B'.
      rewrite !in_set.
      case HB': (B' == B).
      + (* B' = B *)
        move/eqP: HB' ->.
        have ->: is_complete n B.
          by rewrite Hi'.
        rewrite {1}Hi'.
        rewrite HBcorr.
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
            case Hy: (y < i').
            + (* y < i' *)
              rewrite /is_complete in HBcompl.
              move/forallP: HBcompl=> HBcompl.
              move: (HBcompl y)=> HBcompl2.
              rewrite Hy /= in HBcompl2.
              move/existsP: HBcompl2=> [k' /eqP Hk'].
              rewrite -Hi' in Hk'.
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
              rewrite Htrivial /= andbF andbC andbF implybF /get_coord in Hcorr'''.
              by apply negbTE.
            + (* y >= i' *)
              rewrite /is_correct in H2.
              move/forallP: H2=>H2.
              move: (H2 x)=> /forallP H2'.
              move: (H2' y)=> H2''.
              rewrite {3}Hi' Hy andbF andbC andbF implybF /get_coord in H2''.
              by apply negbTE.
        rewrite Habs in HB'.
        move/eqP: HB'=>HB'.
        by rewrite //.
    by rewrite cards1.
  + (* col != full *)
    set P := (~: (((make_ld n B i') :|: (make_rd n B i')) :|: (make_col n B))).
    rewrite (H _ _ _ _ _ _ _ B i' _ _ _ _ _ _ _ P)=> //.
    rewrite addn0.
    have ->: [set B' in valid_pos n | board_included n B B' & board_possible n P B' i']
           = [set B' in valid_pos n | board_included n B B'].
      rewrite -setP /eq_mem=> i.
      rewrite !in_set.
      admit. (* For each complete & correct board, there is one bit in P / poss *)
    rewrite //.
    rewrite -(leq_add2r 1) !addn1 -Hfuel' Hfuel //.
    apply compl_repr.
    apply union_repr=> //.
    by apply union_repr.
Admitted.

Theorem queens_correct: forall n, n <= BitsRepr.wordsize -> exists f, countNQueens n f = #|valid_pos n|.
Proof.
  move=> n ltn_n.
  move: (queensAux_correct n ltn_n)=> [f H].
  have Hempty: forall x y, get_coord n empty_board x y = false.
    move=> x y.
    by rewrite /get_coord !tnth_mktuple.
  exists f.
  rewrite /countNQueens.
  rewrite (H _ _ _ _ _ _ empty_board ord0)=> //.
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
  by apply spec.subset_repr.
Qed.

Cd "extraction".

Separate Extraction countNQueens.
