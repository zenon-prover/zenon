(*  Copyright 2005 INRIA  *)
(*  $Id: progress.mli,v 1.2 2005-11-05 11:13:17 doligez Exp $  *)

type progress = No | Bar | Msg;;
val level : progress ref;;
val do_progress : (unit -> unit) -> unit;;
val end_progress : string -> unit;;
