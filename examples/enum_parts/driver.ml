open Enum_parts

let rec btos n =
  if n = 0 then "0"
  else if n = 1 then "1"
  else btos (n / 2) ^ (btos (n mod 2))

(* TODO: also prove? *)
let initial n = (1 lsl n) - 1

(* TODO: also prove? *)
let enum_correct x n = ((x lsr n) = 0)

let () =
  let n = 7 in
  let x = ref (initial 5) in
  while (enum_correct !x n) do
    Printf.printf "%s\n" (btos !x);
    x := enumNext !x;
  done
