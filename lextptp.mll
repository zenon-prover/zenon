(*  Copyright 2005 INRIA  *)
{
Version.add "$Id: lextptp.mll,v 1.2 2005-11-05 11:13:17 doligez Exp $";;

open Parsetptp;;
open Lexing;;

}

let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\009' '\012']
let stringchar = [^ '\000'-'\031' '\"' '\127'-'\255']
let upperid = [ 'A' - 'Z' ]
let lowerid = [ 'a' - 'z' '0'-'9']
let idchar = [ 'A' - 'Z' 'a' - 'z' '0' - '9' '_' ]

rule token = parse
  | "%@" ([^ '\010' '\013'] * as annot)
                     { TPANNOT annot }
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
  | "\'" stringchar + "\'" {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }
  | lowerid idchar *   { LIDENT (Lexing.lexeme lexbuf) }
  | upperid idchar *   { UIDENT (Lexing.lexeme lexbuf) }

  | eof              { EOF }
  | _                {
      let msg = "bad character " ^ Lexing.lexeme lexbuf
      in raise (Error.Lex_error msg)
    }
