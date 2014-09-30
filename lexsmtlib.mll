{
open Smtlib_parse;;
}

rule token = parse
    | ['\t' ' ' ]+      { token lexbuf }
    | ';'  (_ # '\n')*  { token lexbuf }
    | ['\n']+ as str    { line := (!line + (String.length str)); token lexbuf }
    | "_"               { UNDERSCORE }
    | "("               { LPAREN }
    | ")"               { RPAREN }
    | "as"              { AS }
    | "let"             { LET }
    | "forall"          { FORALL }
    | "exists"          { EXISTS }
    | "!"               { EXCLIMATIONPT }
    | "set-logic"       { SETLOGIC }
    | "set-option"      { SETOPTION }
    | "set-info"        { SETINFO }
    | "declare-sort"    { DECLARESORT }
    | "define-sort"     { DEFINESORT }
    | "declare-fun"     { DECLAREFUN }
    | "define-fun"      { DEFINEFUN }
    | "push"            { PUSH }
    | "pop"             { POP }
    | "assert"          { ASSERT }
    | "check-sat"       { CHECKSAT }
    | "get-assertions"  { GETASSERT }
    | "get-proof"       { GETPROOF }
    | "get-unsat-core"  { GETUNSATCORE }
    | "get-value"       { GETVALUE }
    | "get-assignment"  { GETASSIGN }
    | "get-option"      { GETOPTION }
    | "get-info"        { GETINFO }
    | "exit"            { EXIT }
    |  '#' 'x' ['0'-'9' 'A'-'F' 'a'-'f']+  as str
                        { HEXADECIMAL(str) }
    |  '#' 'b' ['0'-'1']+  as str
                        { BINARY(str) }
    |  '|' ([ '!'-'~' ' ' '\n' '\t' '\r'] # ['\\' '|'])* '|' as str
                        { ASCIIWOR(str) }
    |  ':' ['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']+  as str
                        { KEYWORD(str) }
    |  ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '=''%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@'] ['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '=''%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']*  as str
                        { SYMBOL(str) }
    |  '"' (([ '!'-'~' ' ' '\n' '\t' '\r' ] # ['\\' '"']) | ('\\' ['!'-'~' ' ' '\n' '\t' '\r'] ))* '"' as str
                        { STRINGLIT(str) }
    |  ( '0' | ['1'-'9'] ['0'-'9']* )  as str
                        { NUMERAL(str) }
    |  ( '0' | ['1'-'9'] ['0'-'9']* ) '.' ['0'-'9']+ as str
                        { DECIMAL(str) }
    | eof               { EOF }
    | _                 { failwith((Lexing.lexeme lexbuf) ^ ": lexing error on line "^(string_of_int !line))} {}
