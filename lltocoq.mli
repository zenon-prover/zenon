(*  Copyright 2004 INRIA  *)
(* $Id: lltocoq.mli,v 1.2 2004-05-28 19:55:17 delahaye Exp $ *)

val produce_proof : bool -> string option -> bool -> Llproof.proof -> int
