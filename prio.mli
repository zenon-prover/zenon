(*  Copyright 2004 INRIA  *)
(* $Id: prio.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $ *)

type t = {
  shape : int;  (* ignored for formulas *)
  origin : int;
  weight1 : int;
  weight2 : int;
};;

val make : int -> t;;

val update : t -> int -> int -> int -> t;;
(* update old newshape weight_increment secondary_weight *)

val sh_close1 : int;;
val sh_close2 : int;;
val sh_closeeq : int;;
val sh_false : int;;
val sh_nottrue : int;;
val sh_notnot : int;;
val sh_def : int;;
val sh_and : int;;
val sh_notor : int;;
val sh_notimpl : int;;
val sh_or : int;;
val sh_impl : int;;
val sh_notand : int;;
val sh_equiv : int;;
val sh_notequiv : int;;
val sh_notall : int;;
val sh_ex : int;;
val sh_all_meta : int;;
val sh_notex_meta : int;;
val sh_all_inst : int;;
val sh_notex_inst : int;;
val sh_all_partial : int;;
val sh_notex_partial : int;;
val sh_equal_notequal : int;;
val sh_p_notp : int;;
val sh_notequal : int;;

val weight_alpha : int;;
val weight_def : int;;
val weight_beta : int;;
val weight_beta_double : int;;
val weight_gamma : int;;
val weight_delta : int;;
val weight_inst : int;;
val weight_part : int;;
val weight_notequiv : int;;
val weight_notequal : int;;
val weight_equal_notequal : int;;
val weight_meta_neq : int;;
val weight_metameta : int;;
val weight_critpair : int;;
