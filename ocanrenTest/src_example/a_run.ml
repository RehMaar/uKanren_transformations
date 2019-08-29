open Std

open Tester

open A

(*
let rec show_nat f = function
  | Z   -> "Z"
  | S x -> Printf.sprintf "S%s" (f x)

let rec showNat  x = show_nat showNat x
let rec showGnat x = show logic (show_nat showGnat) x

let rec natReify x = For_gnat.reify natReify x

let run x = runR (List.reify natReify)
                 (show List.ground showNat)
                 (show List.logic showGnat) x


let rec ll f = function
  | []      -> nil ()
  | x :: xs -> f x % ll f xs


let llp = ll (fun (x, y) -> pair x y)


let a = z ()
let b = s a
let c = s b
let d = s c

let graph1 = [a, b; b, c; c, a; b, d; d, a]
*)


let _ = Printf.printf "Hello!\n"
