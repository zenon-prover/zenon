(*  Copyright 2004 INRIA  *)
(*  $Id: version.mli,v 1.1 2004-04-29 13:04:52 doligez Exp $  *)

(* whole-program release and version numbers *)

val major : int;;
val minor : int;;
val bugfix : int;;
val date : string;;
val number : int;;

val short : string;;
val full : string;;

(* file-by-file CVS version strings *)

val add : string -> unit;;
val print_cvs : out_channel -> unit;;
