(*  Copyright 2004 INRIA  *)
(*  $Id: tptp.mli,v 1.3.2.1 2005-10-03 10:22:30 doligez Exp $  *)

open Phrase;;

val get_thm_name: unit -> string;;
val process_annotations : phrase list -> phrase list;;
val translate : string list -> tpphrase list -> phrase list;;
