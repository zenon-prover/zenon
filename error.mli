(*  Copyright 2005 INRIA  *)
(*  $Id: error.mli,v 1.6 2012-04-24 17:32:04 doligez Exp $  *)

val warnings_flag : bool ref;;
val got_warning : bool ref;;
val err_file : string ref;;

val set_header : string -> unit;;
val warn : string -> unit;;
val err : string -> unit;;
val errpos : Lexing.position -> string -> unit;;

exception Lex_error of string;;
exception Abort;;
