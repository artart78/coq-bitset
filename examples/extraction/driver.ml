open Top

let _ = 
  for i = 1 to 30 do
    let start = Unix.gettimeofday () in
    let res = countNQueens i in
    Printf.printf "%d [%f]\n" res (Unix.gettimeofday () -. start);
    flush stdout
  done
(* Should print:
    1 0 0 2 10 4 40 92 352 724 2680 14200 73712 365596 
*)
