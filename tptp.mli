(*  Copyright 2004 INRIA  *)
(*  $Id: tptp.mli,v 1.4 2005-06-23 07:07:59 prevosto Exp $  *)

val process_annotations: Phrase.phrase list -> Phrase.phrase list
val translate : string list -> Phrase.tpphrase list -> Phrase.phrase list;;
