(*  Copyright 2004 INRIA  *)
(* $Id: lexer.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $ *)

val token : Lexing.lexbuf -> Parser.token;;
val tptoken : Lexing.lexbuf -> Parser.token;;
val coqtoken : Lexing.lexbuf -> Parser.token;;
