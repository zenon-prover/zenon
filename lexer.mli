(*  Copyright 2004 INRIA  *)
(*  $Id: lexer.mli,v 1.2 2004-04-29 13:04:52 doligez Exp $  *)

val token : Lexing.lexbuf -> Parser.token;;
val tptoken : Lexing.lexbuf -> Parser.token;;
val coqtoken : Lexing.lexbuf -> Parser.token;;
