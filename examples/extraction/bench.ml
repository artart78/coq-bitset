let rec countNQueensEachPos poss ld col rd curCount full =
  if (poss land full) = 0 then
    curCount
  else
    let bit = poss land (- poss) in
    let count = countNQueensAux ((ld lor bit) lsr 1) (col lor bit) ((rd lor bit) lsl 1) full in
    countNQueensEachPos (poss land (lnot bit)) ld col rd (curCount + count) full
and countNQueensAux ld col rd full =
  if (col = full) then
  	1
  else
    let poss = lnot (ld lor rd lor col) in
    countNQueensEachPos poss ld col rd 0 full

let countNQueens n =
  countNQueensAux 0 0 0 ((1 lsl n) - 1)

let _ = 
  for i = 1 to 20 do
  	let start = Unix.gettimeofday () in
  	let res = countNQueens i in
  	Printf.printf "%d [%f]\n" res (Unix.gettimeofday () -. start);
  	flush stdout
  done
(* Should print:
    1 0 0 2 10 4 40 92 352 724 2680 14200 73712 365596 
*)
