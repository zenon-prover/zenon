(* output oc phrases ppphrases llp filename contextoutput
 outputs the dedutki proof from phrases (ie before preprocessing of extensions),
ppphrases (ie after preprocessing of extensions), llp an llproof, filename,
and contextoutput a boolean indicating whether the context should be printed *)

val output : out_channel -> Phrase.phrase list -> Phrase.phrase list
  -> Llproof.proof-> string -> bool -> unit
