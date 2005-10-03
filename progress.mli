(*  Copyright 2005 INRIA  *)
(*  $Id: progress.mli,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $  *)

type progress = No | Bar | Msg;;
val level : progress ref;;
val do_progress : (unit -> unit) -> unit;;
val end_progress : string -> unit;;
