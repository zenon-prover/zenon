(*  Copyright 2004 INRIA  *)
{
Version.add "$Id: lexer.mll,v 1.11 2004-09-28 13:12:58 doligez Exp $";;

open Parser;;
open Lexing;;

}

let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\009' '\012']
let blank = [' ' '\009' '\012' '\010' '\013']
let identchar =  [^ '\000'-'\031' '\"' '\127'-'\255' '(' ')' ' ' '#' ';' '$']
let stringchar = [^ '\000'-'\031' '\"' '\127'-'\255']
let upper = [ 'A' - 'Z' ]
let lower = [ 'a' - 'z' ]
let tpidchar = [ 'A' - 'Z' 'a' - 'z' '0' - '9' '_' ]
let coqidchar = [ 'A' - 'Z' 'a' - 'z' '0' - '9' '_' '`' ]

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

  | identchar + { IDENT (Lexing.lexeme lexbuf) }

  | eof         { EOF }
  | _           { raise (Failure ("unknown char " ^ Lexing.lexeme lexbuf)) }

and tptoken = parse
  | '%' [^ '\010' '\013'] * { tptoken lexbuf }
  | newline     { lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                    pos_bol = lexbuf.lex_curr_p.pos_cnum;
                    pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
                  };
                  tptoken lexbuf }
  | space +          { tptoken lexbuf }
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
  | "<~>"            { XOR }
  | "~|"             { NOR }
  | "~&"             { NAND }
  | "++"             { POSITIVE }
  | "--"             { NEGATIVE }
  | "include"        { INCLUDE }
  | "input_clause"   { INPUT_CLAUSE }
  | "input_formula"  { INPUT_FORMULA }
  | "equal"          { EQUAL }
  | "\'" stringchar + "\'" {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }
  | (lower | ['0' - '9']) tpidchar *
                      { LIDENT (Lexing.lexeme lexbuf) }
  | upper tpidchar *  { UIDENT (Lexing.lexeme lexbuf) }

  | eof               { EOF }
  | _           { raise (Failure ("unknown char " ^ Lexing.lexeme lexbuf)) }

and coqtoken = parse
  | '#' [^ '\010' '\013'] * { coqtoken lexbuf }
  | ';' [^ '\010' '\013'] * { coqtoken lexbuf }
  | newline     { lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                    pos_bol = lexbuf.lex_curr_p.pos_cnum;
                    pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
                  };
                  coqtoken lexbuf }
  | space +                 { coqtoken lexbuf }
  | "Local"                 { LOCAL }
  | "Let"                   { LOCAL }
  | "(* to be proved *)"    { TOBE }
  | "(* Qed *)."            { QED }
  | "%%begin-auto-proof" blank* newline blank*
    "%%location:" blank* '[' [^ ']']* ']' blank* newline blank*
    "%%name:" blank* (identchar+ as name) blank* newline blank*
    "%%statement" blank* newline
                { lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                    pos_bol = lexbuf.lex_curr_p.pos_cnum;
                    pos_lnum = lexbuf.lex_curr_p.pos_lnum + 4;
                  };
                  BEGINPROOF name }
  | "%%end-auto-proof"      { ENDPROOF }
  | "(*"                    { coqcomment lexbuf }
  | "By"                    { BY }
  | "By def"                { BYDEF }
  | "forall"                { FORALL }
  | "let"                   { LET }
  | "in"                    { IN }
  | "and"                   { AND }
  | "or"                    { OR }
  | "/\\"                   { SLASHBACKSLASH }
  | "\\/"                   { BACKSLASHSLASH }
  | "if"                    { IF }
  | "then"                  { THEN }
  | "else"                  { ELSE }
  | "fun"                   { FUN }
  | "="                     { EQUAL }
  | '('                     { OPEN }
  | ')'                     { CLOSE }
  | ':'                     { COLON }
  | ":="                    { COLONEQUAL }
  | '['                     { LBRACKET }
  | ']'                     { RBRACKET }
  | "->"                    { ARROW }
  | "=>"                    { FUNARROW }
  | "<->"                   { DOUBLEARROW }
  | "~"                     { TILDE }
  | "."                     { DOT }
  | ","                     { COMMA }
  | coqidchar +             { IDENT (Lexing.lexeme lexbuf) }
  | eof                     { EOF }
  | "\"" stringchar + "\"" {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }
  | _           { raise (Failure ("unknown char " ^ Lexing.lexeme lexbuf)) }

and coqcomment = parse
  | "*)"                    { coqtoken lexbuf }
  | [^ '\010' '\013'] *     { coqcomment lexbuf }
  | newline     { lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                    pos_bol = lexbuf.lex_curr_p.pos_cnum;
                    pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
                  };
                  coqcomment lexbuf }
