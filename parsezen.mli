type token =
  | OPEN
  | CLOSE
  | EOF
  | IDENT of (string)
  | STRING of (string)
  | INT of (int)
  | ALL
  | AND
  | DEF
  | EQUAL
  | EQUIV
  | EX
  | FALSE
  | FIX
  | FIXPOINT
  | GOAL
  | HYP
  | IMPLY
  | INCLUDE
  | INDSET
  | INDPROP
  | LAMBDA
  | LET
  | MATCH
  | NOT
  | OR
  | RIMPLY
  | SELF
  | SIG
  | TAU
  | TRUE

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Phrase.zphrase list
