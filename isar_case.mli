(*  Copyright 2009 INRIA  *)
(*  $Id: isar_case.mli,v 1.1 2009-09-11 13:24:21 doligez Exp $  *)

(* Utility for printing and proving the lemmas for the CASE rule
   for the Isar format output. *)

val print_case : string -> int -> bool -> out_channel -> unit;;
