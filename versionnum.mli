(*  Copyright 2008 INRIA  *)
(*  $Id: versionnum.mli,v 1.1 2008-10-22 14:54:35 doligez Exp $  *)

(* whole-program release and version numbers *)

val number : int;;
val date : string;;

val major : int;;
val minor : int;;
val bugfix : int;;

val short : string;;
val full : string;;
