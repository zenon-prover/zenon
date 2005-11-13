(*  Copyright 2005 INRIA  *)
(*  $Id: error.mli,v 1.4 2005-11-13 22:49:11 doligez Exp $  *)

val warnings_flag : bool ref;;
val err_file : string ref;;

val set_header : string -> unit;;
val warn : string -> unit;;
val err : string -> unit;;
val errpos : Lexing.position -> string -> unit;;

exception Lex_error of string;;
exception Abort;;
