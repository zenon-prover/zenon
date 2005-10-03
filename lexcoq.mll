(*  Copyright 2005 INRIA  *)
{
Version.add "$Id: lexcoq.mll,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $";;

open Parsecoq;;
open Lexing;;

exception Lex_error of string;;

}

let newline = ('\010' | '\013' | "\013\010")
let inline = [^ '\010' '\013' ]
let space = [' ' '\009' '\012']
let blank = [' ' '\009' '\012' '\010' '\013']
let stringchar = [^ '\000'-'\031' '\"' '\127'-'\255']
let upper = [ 'A' - 'Z' ]
let lower = [ 'a' - 'z' ]

let idbegin = [ 'A' - 'Z' 'a' - 'z' '_' ]
let idchar = [ 'A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'' ]

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

  | "as"                    { AS }
  | "at"                    { AT }
  | "cofix"                 { COFIX }
  | "Depends"               { DEPENDS }
  | "Definition"            { DEFINITION }
  | "else"                  { ELSE }
  | "end"                   { END }
  | "exists"                { EXISTS }
  | "exists2"               { EXISTS2 }
  | "fix"                   { FIX }
  | "for"                   { FOR }
  | "forall"                { FORALL }
  | "fun"                   { FUN }
  | "if"                    { IF }
  | "IF"                    { UC_IF }
  | "in"                    { IN }
  | "let"                   { LET }
  | "match"                 { MATCH }
  | "mod"                   { MOD }
  | "on"                    { ON }
  | "Parameter"             { PARAMETER }
  | "Prop"                  { PROP }
  | "return"                { RETURN }
  | "Set"                   { SET }
  | "then"                  { THEN }
  | "Type"                  { TYPE }
  | "using"                 { USING }
  | "where"                 { WHERE }
  | "with"                  { WITH }

  | idbegin idchar * ('.' idbegin idchar *) *
      { IDENT (Lexing.lexeme lexbuf) }

  | "%%begin-auto-proof" inline*
      { BEGINPROOF }
  | "%%name:" blank* (idchar+ as name) blank*
      { BEGINNAME name }
  | "%%" idchar* ":" inline*
      { BEGINHEADER }
  | "%%statement" inline*
      { BEGINSTATEMENT }
  | "%%end-auto-proof" inline*
      { ENDPROOF }

  | eof                     { EOF }

  | "\"" stringchar + "\""  {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }

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