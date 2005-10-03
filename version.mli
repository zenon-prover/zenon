(*  Copyright 2004 INRIA  *)
(*  $Id: version.mli,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $  *)

(* whole-program release and version numbers *)

val number : int;;
val date : string;;

val major : int;;
val minor : int;;
val bugfix : int;;

val short : string;;
val full : string;;

(* file-by-file CVS version strings *)

val add : string -> unit;;
val print_cvs : out_channel -> unit;;
