open Bloom

let hash n s =
  let rec hash2 curCount = function
  | -1 -> curCount
  | x when x < 0 -> failwith "meh"
  | x -> (hash2 (curCount + Char.code s.[x]) (x - 1)) mod n
  in hash2 0 (String.length s - 1)
  ;;

let hashlist = [hash 5; hash 7; hash 13; hash 19] ;;

let _ =
  let x = bloomAdd (bloomAdd 0 hashlist "plop") hashlist "yop" in
  Printf.printf "%b %b %b\n" (bloomCheck x hashlist "plop") (bloomCheck x hashlist "yop") (bloomCheck x hashlist "hello")
(* Should print:
    true true false
*)
