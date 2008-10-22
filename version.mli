(*  Copyright 2004 INRIA  *)
(*  $Id: version.mli,v 1.3 2008-10-22 11:51:04 doligez Exp $  *)

(* file-by-file CVS version strings *)

val add : string -> unit;;
val print_cvs : out_channel -> unit;;
