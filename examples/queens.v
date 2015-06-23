From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

Require Import extract repr_op.

Fixpoint countNQueensEachPos (poss: Int63)(ld: Int63)(col: Int63)(rd: Int63)(curCount: nat)(full: Int63)(fuel: nat)
  := match fuel with
     | 0 => 0
     | n'.+1 =>
       if (leq (land poss full) (toInt63 0)) then
         curCount
       else (
         let bit := land poss (lneg poss) in
         let count := countNQueensAux (lsr (lor ld bit) 1) (lor col bit) (lsl (lor rd bit) 1) full n' in
         countNQueensEachPos (land poss (lnot bit)) ld col rd (curCount + count) full n'
       )
     end
with countNQueensAux (ld: Int63)(col: Int63)(rd: Int63)(full: Int63)(fuel: nat)
  := match fuel with
     | 0 => 0
     | n'.+1 =>
       if (leq col full) then
         1
       else (
         let poss := lnot (lor (lor ld rd) col) in
         countNQueensEachPos poss ld col rd 0 full n'
       )
     end.       

Definition countNQueens (n: nat) (fuel: nat)
  := countNQueensAux (toInt63 0) (toInt63 0) (toInt63 0) (ldec (lsl (toInt63 1) n)) fuel.

Extraction "queens.ml" countNQueens.     
