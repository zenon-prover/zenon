(*  Copyright 1997 INRIA  *)
(*  $Id: globals.mli,v 1.8 2005-11-21 18:48:28 doligez Exp $  *)

val debug_flag : bool ref;;

val warnings_flag : bool ref;;
val stats_flag : bool ref;;
val quiet_flag : bool ref;;
val size_limit : float ref;;
val time_limit : float ref;;
val short_flag : bool ref;;
val ctx_flag : bool ref;;
val random_flag : bool ref;;
val random_seed : int ref;;

val inferences : int ref;;
val proof_nodes : int ref;;
val top_num_forms : int ref;;
val stored_lemmas : int ref;;
val num_expr : int ref;;
