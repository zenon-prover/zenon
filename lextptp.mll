(*  Copyright 2005 INRIA  *)
{
Version.add "$Id: lextptp.mll,v 1.6 2010-07-01 16:17:29 doligez Exp $";;

open Lexing;;
open Parsetptp;;
open Printf;;

}

let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\009' '\012']
let stringchar = [^ '\000'-'\031' '\'' '\127'-'\255']
let upperid = [ 'A' - 'Z' ]
let lowerid = [ 'a' - 'z' '0'-'9']
let idchar = [ 'A' - 'Z' 'a' - 'z' '0' - '9' '_' ]

rule token = parse
  | "%@" ([^ '\010' '\013'] * as annot)
                     { ANNOT annot }
  | "%" [^ '\010' '\013'] *
                     { token lexbuf }
  | newline          {
      lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
        pos_bol = lexbuf.lex_curr_p.pos_cnum;
        pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      };
      token lexbuf
    }
  | space +          { token lexbuf }
  | "("              { OPEN }
  | ")"              { CLOSE }
  | "["              { LBRACKET }
  | "]"              { RBRACKET }
  | ","              { COMMA }
  | ":"              { COLON }
  | "."              { DOT }
  | "?"              { EX }
  | "!"              { ALL }
  | "~"              { NOT }
  | "|"              { OR }
  | "&"              { AND }
  | "=>"             { IMPLY }
  | "<="             { RIMPLY }
  | "<=>"            { EQUIV }
  | "="              { EQSYM }
  | "!="             { NEQSYM }
  | "<~>"            { XOR }
  | "~|"             { NOR }
  | "~&"             { NAND }
  | "include"        { INCLUDE }
  | "input_clause"   { INPUT_CLAUSE }
  | "cnf"            { INPUT_CLAUSE }
  | "input_formula"  { INPUT_FORMULA }
  | "fof"            { INPUT_FORMULA }
  | "equal"          { EQUAL }
  | "$true"          { TRUE }
  | "$false"         { FALSE }
  | "\'" stringchar + "\'" {
      let s = Lexing.lexeme lexbuf in
      LIDENT (String.sub s 1 (String.length s - 2))
    }
  | lowerid idchar *   { LIDENT (Lexing.lexeme lexbuf) }
  | upperid idchar *   { UIDENT (Lexing.lexeme lexbuf) }

  | eof              { EOF }
  | _                {
      let msg = sprintf "bad character %C" (Lexing.lexeme_char lexbuf 0) in
      raise (Error.Lex_error msg)
    }
