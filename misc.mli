(*  Copyright 1997 INRIA  *)
(*  $Id: misc.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $  *)

val version : string -> unit;;
val print_versions : unit -> unit;;

val index : int -> 'a -> 'a list -> int;;
