(*  Copyright 2005 INRIA  *)
{
Version.add "$Id: lexzen.mll,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $";;

open Parsezen;;
open Lexing;;

}

let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\009' '\012']
let blank = [' ' '\009' '\012' '\010' '\013']
let identchar =  [^ '\000'-'\031' '\"' '\127'-'\255' '(' ')' ' ' '#' ';' '$']
let stringchar = [^ '\000'-'\031' '\"' '\127'-'\255']
let upper = [ 'A' - 'Z' ]
let lower = [ 'a' - 'z' ]

rule token = parse
  | '#' [^ '\010' '\013'] * { token lexbuf }
  | ';' [^ '\010' '\013'] * { token lexbuf }
  | newline     { lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                    pos_bol = lexbuf.lex_curr_p.pos_cnum;
                    pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
                  };
                  token lexbuf }
  | space +     { token lexbuf }
  | "("         { OPEN }
  | ")"         { CLOSE }
  | '$' ['0' - '9'] + {
      let s = Lexing.lexeme lexbuf in
      let i = int_of_string (String.sub s 1 (String.length s - 1)) in
      INT i
    }
  | "$def"      { DEF }
  | "$goal"     { GOAL }
  | "-."        { NOT }
  | "/\\"       { AND }
  | "\\/"       { OR }
  | "=>"        { IMPLY }
  | "<="        { RIMPLY }
  | "<=>"       { EQUIV }
  | "True"      { TRUE }
  | "False"     { FALSE }
  | "A."        { ALL }
  | "E."        { EX }
  | "t."        { TAU }
  | "="         { EQUAL }
  | "\"" stringchar + "\"" {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }

  | identchar +  { IDENT (Lexing.lexeme lexbuf) }
  | eof         { EOF }
  | _           { let msg = ("bad character " ^ Lexing.lexeme lexbuf)
                  in raise (Error.Lex_error msg)
                }
