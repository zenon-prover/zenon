(*  Copyright 2004 INRIA  *)
(*  $Id: tptp.mli,v 1.5 2005-06-23 13:05:47 prevosto Exp $  *)

val get_thm_name: unit -> string
val process_annotations: Phrase.phrase list -> Phrase.phrase list
val translate : string list -> Phrase.tpphrase list -> Phrase.phrase list;;
