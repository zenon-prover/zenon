(*  Copyright 1997 INRIA  *)
(* $Id: globals.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $ *)

val step_count : int ref;;
(* =< 0 means infinite; otherwise pause after that many steps *)

val warnings_flag : bool ref;;
val stats_flag : bool ref;;
val size_limit : float ref;;
val time_limit : float ref;;

val progress_flag : bool ref;;
val progress : (unit -> unit) -> unit;;

val inferences : int ref;;
val proof_nodes : int ref;;
val top_num_forms : int ref;;
val stored_lemmas : int ref;;
val num_expr : int ref;;

val goal_found : bool ref;;
