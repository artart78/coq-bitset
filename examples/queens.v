From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Require Import bineqs extract repr_op.

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

Definition get_coord (B: BitsRepr.wordsize.-tuple (BitsRepr.wordsize.-tuple bool)) (x: 'I_BitsRepr.wordsize) (y: 'I_BitsRepr.wordsize) := tnth (tnth B x) y.

Definition is_complete n B : bool :=
  [forall k : 'I_BitsRepr.wordsize, (0 <= k < n) ==> [exists k', get_coord B k k' == true]].

Definition is_correct B :=
  [forall i : 'I_BitsRepr.wordsize, forall i' : 'I_BitsRepr.wordsize,
   forall j : 'I_BitsRepr.wordsize, forall j' : 'I_BitsRepr.wordsize,
    ((get_coord B i i') && (get_coord B j j')) ==>
    (i != j) && (i' != j') (* Not on the same horizontal / vertical line *)
    && ((i' < i) ==> (j' < j) ==> (i - i' != j - j')) (* Not on the same right diagonal *)
    && (i + i' != j + j')]. (* Not on the same left diagonal *)

Definition valid_pos n := [set B | is_complete n B && is_correct B].

Definition make_ld B i' := [set i : 'I_BitsRepr.wordsize | [exists j : 'I_BitsRepr.wordsize, exists j' : 'I_BitsRepr.wordsize, (get_coord B j j') && (i + i' == j + j')]].

Definition repr_ld B i' ld
  := native_repr ld (make_ld B i').

Definition make_col B := [set i : 'I_BitsRepr.wordsize | [exists i' : 'I_BitsRepr.wordsize,
       get_coord B i i']].

Definition repr_col B col
  := native_repr col (make_col B).

Definition make_rd B i'
  := [set i : 'I_BitsRepr.wordsize | [exists j : 'I_BitsRepr.wordsize, exists j' : 'I_BitsRepr.wordsize,
     (get_coord B j j') && ((i' < i) ==> (j' < j) ==> (i - i' != j - j'))]].

Definition repr_rd B i' rd
  := native_repr rd (make_rd B i').

Definition repr_full n full
  := native_repr full [set x : 'I_BitsRepr.wordsize | 0 <= x < n].

Definition board_included B B' := [forall x, forall y, get_coord B x y ==> get_coord B' x y].

Definition empty_board := [tuple [tuple false | i < BitsRepr.wordsize] | i < BitsRepr.wordsize].

Definition board_possible (P: {set ordinal_finType BitsRepr.wordsize}) B' i' := [forall i, get_coord B' i i' ==> (i \in P)].

Lemma queensEachPos_correct (n: nat) :
  forall poss ld col rd full B (i': 'I_BitsRepr.wordsize), exists f, forall fuel, fuel >= f ->
    forall curCount, is_correct B ->
      (repr_ld B i' ld) -> (repr_rd B i' rd) -> (repr_col B col) -> (repr_full n full) ->
      forall P, (native_repr poss P) ->
      countNQueensEachPos poss ld col rd curCount full fuel =
        #|[set B' in (valid_pos n) | board_included B B' && board_possible P B' i']| + curCount
with queensAux_correct (n: nat) :
  forall ld col rd full B (i': 'I_BitsRepr.wordsize), exists f, forall fuel, fuel >= f -> is_correct B ->
    (repr_ld B i' ld) -> (repr_rd B i' rd) -> (repr_col B col) -> (repr_full n full) ->
      countNQueensAux ld col rd full fuel =
        #|[set B' in (valid_pos n) | board_included B B']|.
Proof.
  move=> poss ld col rd full B i'.
  set bit := (BitsRepr.land poss (BitsRepr.lneg poss)).
  set ld' := (BitsRepr.lsr (BitsRepr.lor ld bit) 1).
  set col' := (BitsRepr.lor col bit).
  set rd' := (BitsRepr.lsl (BitsRepr.lor rd bit) 1).
  set B' := B. (* 'bit' needs to be added! *)
  set poss' := (BitsRepr.land poss (BitsRepr.lnot bit)).
  have ltn_i': i'.+1 < BitsRepr.wordsize by admit.
  move: (queensAux_correct n ld' col' rd' full B' (Ordinal ltn_i')).
  move=> [f H].
  move: (queensEachPos_correct n poss' ld col rd full B i').
  move=> [f' H'].
  exists ((maxn f f').+1).
  move=> fuel Hfuel curCount HB Hld Hrd Hcol Hfull P HP.
  set P' := P. (* 'bit' needs to be removed! *)
  have Hfuel': fuel = fuel.-1.+1 by admit.
  rewrite Hfuel'.
  rewrite /countNQueensEachPos.
  rewrite -/countNQueensAux.
  rewrite -/countNQueensEachPos.
  case: (BitsRepr.leq (BitsRepr.land poss full) BitsRepr.zero).
  + (* (poss & full) == 0 *)
    have ->: [set B' in valid_pos n | board_included B B' & board_possible P B' i'] = set0.
      admit.
    by rewrite cards0 add0n.
  + (* (poss & full) != 0 *)
    rewrite H=> //.
    rewrite (H' _ _ _ _ _ _ _ _ P')=> //.
    admit. (* Looks weird. *)
    admit. (* Trivial. *)
    admit. (* P' *)
    admit. (* Trivial. *)
    admit. (* ld' *)
    admit. (* col' *)
    admit. (* rd' *)
  (****)
  move=> ld col rd full B i'.
  move: (queensEachPos_correct n (BitsRepr.lnot (BitsRepr.lor (BitsRepr.lor ld rd) col)) ld col rd full B i').
  move=> [f H].
  exists (f.+1).
  move=> fuel Hfuel HB Hld Hrd Hcol Hfull.
  have Hfuel': fuel = fuel.-1.+1 by admit.
  rewrite Hfuel'.
  rewrite /countNQueensAux.
  rewrite -/countNQueensEachPos.
  case Hend: (BitsRepr.leq col full).
  + (* col = full *)
    have ->: [set B' in valid_pos n | board_included B B'] = [set B].
      admit.
    by rewrite cards1.
  + (* col != full *)
    set P := (~: (((make_ld B i') :|: (make_rd B i')) :|: (make_col B))).
    rewrite (H _ _ _ _ _ _ _ _ P)=> //.
    rewrite addn0.
    have ->: [set B' in valid_pos n | board_included B B' & board_possible P B' i']
           = [set B' in valid_pos n | board_included B B'].
      rewrite -setP /eq_mem=> i.
      rewrite !in_set.
      admit.
    rewrite //.
    admit. (* Trivial. *)
    apply compl_repr.
    apply union_repr=> //.
    by apply union_repr.
Admitted.

Theorem queens_correct: forall n, n <= BitsRepr.wordsize -> exists f, countNQueens n f = #|valid_pos n|.
Proof.
  move=> n.
  move: (queensAux_correct n BitsRepr.zero BitsRepr.zero BitsRepr.zero (BitsRepr.ldec (BitsRepr.lsl BitsRepr.one n)) empty_board ord0).
  move=> [f H].
  exists f.
  rewrite /countNQueens.
  rewrite H.
  have ->: [set B' in valid_pos n | board_included empty_board B'] = valid_pos n.
    rewrite -setP /eq_mem=> i.
    rewrite in_set.
    have ->: board_included empty_board i = true.
      rewrite /board_included.
      apply/forallP=> x.
      apply/forallP=> y.
      have ->: get_coord empty_board x y = false.
        by rewrite /get_coord /empty_board !tnth_mktuple.
      by rewrite implyFb.
    by rewrite andbT.
  rewrite //.
  rewrite //.
  rewrite /is_correct.

  apply/forallP=> i.
  apply/forallP=> i'.
  apply/forallP=> j.
  apply/forallP=> j'.
  have ->: get_coord empty_board i i' = false.
    by rewrite /get_coord /empty_board !tnth_mktuple.
  rewrite andbC andbF.
  apply implyFb.
  (* TODO: factorize ld, rd and col *)
  (* ld *)
  rewrite /repr_ld /native_repr.
  exists (zero BitsRepr.wordsize).
  rewrite -{1}fromNat0.
  split.
  exact: BitsRepr.zero_repr.
  have ->: (make_ld empty_board 0) = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    rewrite negb_exists.
    apply/forallP=> j'.
    have ->: get_coord empty_board j j' = false.
      by rewrite /get_coord /empty_board !tnth_mktuple.
    by rewrite andbC andbF.
  apply spec.empty_repr.
  (* rd *)
  rewrite /repr_rd /native_repr.
  exists (zero BitsRepr.wordsize).
  rewrite -{1}fromNat0.
  split.
  exact: BitsRepr.zero_repr.
  have ->: (make_rd empty_board 0) = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    rewrite negb_exists.
    apply/forallP=> j'.
    have ->: get_coord empty_board j j' = false.
      by rewrite /get_coord /empty_board !tnth_mktuple.
    by rewrite andbC andbF.
  apply spec.empty_repr.
  (* col *)
  rewrite /repr_col /native_repr.
  exists (zero BitsRepr.wordsize).
  rewrite -{1}fromNat0.
  split.
  exact: BitsRepr.zero_repr.
  have ->: (make_col empty_board) = set0.
    rewrite -setP /eq_mem=> i.
    rewrite in_set in_set0.
    have ->: false = ~~ true by trivial.
    apply negbRL.
    rewrite negb_exists.
    apply/forallP=> j.
    have ->: get_coord empty_board i j = false.
      by rewrite /get_coord /empty_board !tnth_mktuple.
    by rewrite //.
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
