(*  Copyright 1997 INRIA  *)
(*  $Id: globals.mli,v 1.6 2004-10-15 11:55:03 doligez Exp $  *)

val debug_count : int ref;;
(* =< 0 means infinite; otherwise pause after that many steps *)

val warnings_flag : bool ref;;
val stats_flag : bool ref;;
val quiet_flag : bool ref;;
val size_limit : float ref;;
val time_limit : float ref;;
val short_flag : bool ref;;
val ctx_flag : bool ref;;

type progress = Progress_none | Progress_bar | Progress_messages;;
val progress_level : progress ref;;
val do_progress : (unit -> unit) -> unit;;
val end_progress : string -> unit;;

val inferences : int ref;;
val proof_nodes : int ref;;
val top_num_forms : int ref;;
val stored_lemmas : int ref;;
val num_expr : int ref;;

val goal_found : bool ref;;
