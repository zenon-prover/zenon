(*  Copyright 2004 INRIA  *)
(*  $Id: lexer.mli,v 1.3 2004-10-29 08:40:36 doligez Exp $  *)

exception Lex_error of string;;

val token : Lexing.lexbuf -> Parser.token;;
val tptoken : Lexing.lexbuf -> Parser.token;;
val coqtoken : Lexing.lexbuf -> Parser.token;;
