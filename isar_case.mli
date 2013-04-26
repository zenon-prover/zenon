(*  Copyright 2009 INRIA  *)
(*  $Id: isar_case.mli,v 1.2 2010-05-10 14:37:18 doligez Exp $  *)

(* Utility for printing and proving the lemmas for the CASE rule
   for the Isar format output.
   Also for the recordset intro rule.
*)

val print_case : string -> int -> bool -> out_channel -> unit;;

val print_record : string -> int -> out_channel -> unit;;
