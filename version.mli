(*  Copyright 2004 INRIA  *)
(*  $Id: version.mli,v 1.2 2005-11-05 11:13:17 doligez Exp $  *)

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
