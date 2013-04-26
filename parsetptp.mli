type token =
  | EQUIV
  | IMPLY
  | RIMPLY
  | AND
  | OR
  | NOT
  | TRUE
  | FALSE
  | ALL
  | EX
  | OPEN
  | CLOSE
  | EOF
  | INCLUDE
  | DOT
  | INPUT_CLAUSE
  | INPUT_FORMULA
  | LBRACKET
  | RBRACKET
  | LIDENT of (string)
  | UIDENT of (string)
  | STRING of (string)
  | POSITIVE
  | NEGATIVE
  | COMMA
  | EQSYM
  | NEQSYM
  | COLON
  | XOR
  | NOR
  | NAND
  | ANNOT of (string)

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Phrase.tpphrase list
