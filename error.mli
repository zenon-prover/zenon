(*  Copyright 2005 INRIA  *)
(*  $Id: error.mli,v 1.2 2005-11-05 11:13:17 doligez Exp $  *)

val warnings_flag : bool ref;;
val err_file : string ref;;

val set_header : string -> unit;;
val warn : string -> unit;;

exception Lex_error of string;;
