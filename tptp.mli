(*  Copyright 2004 INRIA  *)
(*  $Id: tptp.mli,v 1.6 2005-11-05 11:13:17 doligez Exp $  *)

open Phrase;;

val get_thm_name: unit -> string;;
val process_annotations : phrase list -> phrase list;;
val translate : string list -> tpphrase list -> phrase list;;
