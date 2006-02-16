(*  Copyright 2005 INRIA  *)
{
Version.add "$Id: lexcoq.mll,v 1.6 2006-02-16 09:22:45 doligez Exp $";;

open Parsecoq;;
open Lexing;;

exception Lex_error of string;;

}

let newline = ('\010' | '\013' | "\013\010")
let inline = [^ '\010' '\013' ]
let space = [' ' '\009' '\012']
let stringchar = [^ '\000'-'\031' '\"' '\127'-'\255']
let upper = [ 'A' - 'Z' ]
let lower = [ 'a' - 'z' ]

let idstart = [ 'A' - 'Z' 'a' - 'z' '_' ]
let idchar = [ 'A' - 'Z' 'a' - 'z' '0' - '9' '_' ]

rule token = parse

  | "(*"                    { comment lexbuf }
  | newline                 {
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
        pos_bol = lexbuf.lex_curr_p.pos_cnum;
        pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      };
      token lexbuf
    }
  | space +                 { token lexbuf }
  | "!"                     { BANG_ }
  | "%"                     { PERCENT_ }
  | "&"                     { AMPER_ }
  | "&&"                    { AMPER_AMPER_ }
  | "("                     { LPAREN_ }
  | "()"                    { LPAREN_RPAREN_ }
  | ")"                     { RPAREN_ }
  | "*"                     { STAR_ }
  | "+"                     { PLUS_ }
  | "++"                    { PLUS_PLUS_ }
  | ","                     { COMMA_ }
  | "-"                     { DASH_ }
  | "->"                    { DASH_GT_ }
  | "."                     { PERIOD_ }
  | ".("                    { PERIOD_LPAREN_ }
  | ".."                    { PERIOD_PERIOD_ }
  | "/"                     { SLASH_ }
  | "/\\"                   { SLASH_BACKSL_ }
  | ":"                     { COLON_ }
  | "::"                    { COLON_COLON_ }
  | ":<"                    { COLON_LT_ }
  | ":="                    { COLON_EQ_ }
  | ":>"                    { COLON_GT_ }
  | ";"                     { SEMI_ }
  | "<"                     { LT_ }
  | "<-"                    { LT_DASH_ }
  | "<->"                   { LT_DASH_GT_ }
  | "<:"                    { LT_COLON_ }
  | "<="                    { LT_EQ_ }
  | "<>"                    { LT_GT_ }
  | "="                     { EQ_ }
  | "=>"                    { EQ_GT_ }
  | "=_D"                   { EQ_UNDER_D_ }
  | ">"                     { GT_ }
  | ">->"                   { GT_DASH_GT_ }
  | ">="                    { GT_EQ_ }
  | "?"                     { QUEST_ }
  | "?="                    { QUEST_EQ_ }
  | "@"                     { AROBAS_ }
  | "["                     { LBRACK_ }
  | "\\/"                   { BACKSL_SLASH_ }
  | "]"                     { RBRACK_ }
  | "^"                     { HAT_ }
  | "{"                     { LBRACE_ }
  | "|"                     { BAR_ }
  | "|-"                    { BAR_DASH_ }
  | "||"                    { BAR_BAR_ }
  | "}"                     { RBRACE_ }
  | "~"                     { TILDE_ }

  | "(*_MUST_USE_*)"        { MUSTUSE }

  | "Depends"               { DEPENDS }
  | "on"                    { ON }

  | "Definition"            { DEFINITION }
  | "else"                  { ELSE }
  | "end"                   { END }
  | "exists"                { EXISTS }
  | "False"                 { FALSE }
  | "forall"                { FORALL }
  | "fun"                   { FUN }
  | "if"                    { IF }
  | "in"                    { IN }
  | "Inductive"             { INDUCTIVE }
  | "let"                   { LET }
  | "match"                 { MATCH }
  | "Parameter"             { PARAMETER }
  | "Set"                   { SET }
  | "then"                  { THEN }
  | "Theorem"               { THEOREM }
  | "True"                  { TRUE }
  | "with"                  { WITH }

  | idstart idchar * ('.' idstart idchar *) *
      { IDENT (Lexing.lexeme lexbuf) }

  | "%%begin-auto-proof" inline*
      { BEGINPROOF }
  | "%%name:" space* (idchar+ as name) space*
      { BEGINNAME name }
  | "%%" idchar* ":" inline*
      { BEGINHEADER }
  | "%%end-auto-proof" inline*
      { ENDPROOF }

  | eof                     { EOF }

  | "\"" stringchar + "\""  {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }

  | [ '0'-'9' ]+
      { NUM (Lexing.lexeme lexbuf) }

  | _                       {
      let msg = "bad character " ^ Lexing.lexeme lexbuf in
      raise (Error.Lex_error msg)
    }

and comment = parse
  | "*)"                    { token lexbuf }
  | inline                  { comment lexbuf }
  | newline                 {
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
        pos_bol = lexbuf.lex_curr_p.pos_cnum;
        pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      };
      comment lexbuf
    }
