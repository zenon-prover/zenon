(*  Copyright 2005 INRIA  *)
(*  $Id: error.mli,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $  *)

val warnings_flag : bool ref;;
val err_file : string ref;;

val set_header : string -> unit;;
val warn : string -> unit;;

exception Lex_error of string;;
