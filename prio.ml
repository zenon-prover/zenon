(*  Copyright 2004 INRIA  *)
Version.add "$Id: prio.ml,v 1.4 2004-09-28 13:12:58 doligez Exp $";;

type shape =
  | Close
  | Alpha1
  | Delta
  | Alpha2
  | Beta1
  | Gamma_meta
  | Beta2
  | Correl
  | Gamma_inst of Expr.expr
  | Gamma_inst_partial
;;

type t = int;;

let max_size accu l =
  List.fold_left (fun a e -> max a (Expr.size e)) accu l
;;

let m = 1.0e5;;
let d = 0.0;;
let s = 1.0;;

let make depth shape branches =
  let size () = s *. float (Array.fold_left max_size 0 branches) in
  let dp = float depth in
  let result = match shape with
    | Close -> 0.0
    | Alpha1 | Delta | Alpha2 -> 1.0 *. m +. dp *. d +. size ()
    | Beta1 | Gamma_meta | Beta2 -> 10.0 *. m +. dp *. d +. size ()
    | Correl -> 100.0 *. m +. dp *. d +. size ()
    | Gamma_inst e -> 1000.0 *. m +. dp *. d +. s *. float (Expr.size e)
    | Gamma_inst_partial -> 1000.0 *. m +. dp *. d +. size ()
  in int_of_float result
;;
