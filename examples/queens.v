From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits.

Require Import extract repr_op.

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

Definition get_coord {n} (B: n.-tuple (n.-tuple bool)) (x: 'I_n) (y: 'I_n) := tnth (tnth B x) y.

Definition is_complete (n: nat) B : bool :=
  [forall k, exists k', get_coord (n := n) B k k' == true].

Definition is_correct (n: nat) B :=
  [forall i in 'I_n, forall i' in 'I_n, forall j in 'I_n, forall j' in 'I_n, (i' < i) ==> (j' < j) ==>
    (get_coord B i i' == true && get_coord B j j' == true) ==>
    (i != j) && (i' != j') && (i - i' != j - j')].

Definition valid_pos (n: nat) := [set B | is_complete n B && is_correct n B].

Theorem queens_correct: forall n, exists f, countNQueens n f = #|valid_pos n|.
Proof.
Admitted.

Cd "extraction".

Separate Extraction countNQueens.
