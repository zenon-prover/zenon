(*  Copyright 2005 INRIA  *)
{
Version.add "$Id: lexzen.mll,v 1.4 2006-02-16 09:22:46 doligez Exp $";;

open Parsezen;;
open Lexing;;

}

let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\009' '\012']
let idstart = ['A'-'Z' 'a'-'z' '_']
let idchar =  ['A'-'Z' 'a'-'z' '_' '0'-'9']
let stringchar = [^ '\000'-'\031' '\"' '\127'-'\255']

rule token = parse
  | '#' [^ '\010' '\013'] * { token lexbuf }
  | ';' [^ '\010' '\013'] * { token lexbuf }
  | newline     {
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
        pos_bol = lexbuf.lex_curr_p.pos_cnum;
        pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      };
      token lexbuf
    }
  | space +     { token lexbuf }
  | "("         { OPEN }
  | ")"         { CLOSE }
  | '$' ['0' - '9'] + {
      let s = Lexing.lexeme lexbuf in
      let i = int_of_string (String.sub s 1 (String.length s - 1)) in
      INT i
    }

  | "$def"      { DEF }
  | "$inductive"{ INDUCTIVE }
  | "$sig"      { SIG }
  | "$goal"     { GOAL }
  | "$match"    { MATCH }

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

  | "\"" stringchar* "\"" {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }

  | idstart idchar* { IDENT (Lexing.lexeme lexbuf) }

  | eof         { EOF }
  | _ {
      let c = Lexing.lexeme_char lexbuf 0 in
      let msg = Printf.sprintf "bad character '%s'" (Char.escaped c) in
      raise (Error.Lex_error msg)
    }
