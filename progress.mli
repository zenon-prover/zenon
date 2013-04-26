(*  Copyright 2005 INRIA  *)
(*  $Id: progress.mli,v 1.3 2008-10-24 13:36:36 doligez Exp $  *)

type progress = No | Bar | Msg;;
val level : progress ref;;
val do_progress : (unit -> unit) -> char -> unit;;
val end_progress : string -> unit;;
