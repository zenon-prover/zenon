(*  Copyright 2004 INRIA  *)
Version.add "$Id: prio.ml,v 1.2 2004-04-29 13:04:52 doligez Exp $";;

type t = {
  shape : int;  (* ignored for formulas *)
  origin : int;
  weight1 : int;
  weight2 : int;
};;

let make orig = {
  shape = 0;
  origin = orig;
  weight1 = 0;
  weight2 = 0;
};;

let update old shape weight_incr weight2 =
  { old with
    shape = shape;
    weight1 = old.weight1 + weight_incr;
    weight2 = weight2;
  }
;;

(* closing nodes *)
let sh_close1 = 0
and sh_close2 = 0
and sh_closeeq = 0
and sh_false = 0
and sh_nottrue = 0
(* alpha nodes with 1 formula *)
and sh_notnot = 1
and sh_def = 1
(* alpha nodes with 2 formulas *)
and sh_and = 2
and sh_notor = 2
and sh_notimpl = 2
(* beta nodes with 1 formula per branch *)
and sh_or = 3
and sh_impl = 3
and sh_notand = 3
(* beta nodes with 2 formulas per branch *)
and sh_equiv = 4
and sh_notequiv = 4
(* gamma nodes *)
and sh_notall = 1
and sh_ex = 1
(* delta nodes *)
and sh_all_meta = 3
and sh_notex_meta = 3
and sh_all_inst = 5
and sh_notex_inst = 5
and sh_all_partial = 5
and sh_notex_partial = 5
(* inequality nodes *)
and sh_equal_notequal = 5
and sh_p_notp = 5
and sh_notequal = 5
;;
(* note: there must be no shape number greater than sh_all_inst/sh_notex_inst *)


let weight_alpha = 1;;
let weight_def = 1;;
let weight_beta = 1;;
let weight_beta_double = 0;;
let weight_gamma = 1;;
let weight_delta = 1;;

let weight_inst = 10;;
let weight_part = 100;;
let weight_notequiv = 10;;
let weight_notequal = 10;;
let weight_equal_notequal = 20;;

let weight_meta_neq = 200;;
let weight_metameta = 200;;
let weight_critpair = 1000;;
