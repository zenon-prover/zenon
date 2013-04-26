type token =
  | IDENT of (string)
  | STRING of (string)
  | NUM of (string)
  | BANG_
  | PERCENT_
  | AMPER_
  | AMPER_AMPER_
  | LPAREN_
  | LPAREN_RPAREN_
  | RPAREN_
  | STAR_
  | PLUS_
  | PLUS_PLUS_
  | COMMA_
  | DASH_
  | DASH_GT_
  | PERIOD_
  | PERIOD_LPAREN_
  | PERIOD_PERIOD_
  | SLASH_
  | SLASH_BACKSL_
  | COLON_
  | COLON_COLON_
  | COLON_LT_
  | COLON_EQ_
  | COLON_GT_
  | SEMI_
  | LT_
  | LT_DASH_
  | LT_DASH_GT_
  | LT_COLON_
  | LT_EQ_
  | LT_GT_
  | EQ_
  | EQ_GT_
  | EQ_UNDER_D_
  | GT_
  | GT_DASH_GT_
  | GT_EQ_
  | QUEST_
  | QUEST_EQ_
  | AROBAS_
  | LBRACK_
  | BACKSL_SLASH_
  | RBRACK_
  | HAT_
  | LBRACE_
  | BAR_
  | BAR_DASH_
  | BAR_BAR_
  | RBRACE_
  | TILDE_
  | MUSTUSE
  | DEFINITION
  | DEPENDS
  | ELSE
  | END
  | EXISTS
  | FALSE
  | FIX
  | FIXPOINT
  | FORALL
  | FUN
  | FUNCTION
  | IF
  | IN
  | INDUCTIVE
  | LET
  | MATCH
  | ON
  | PARAMETER
  | STRUCT
  | THEN
  | THEOREM
  | TRUE
  | WITH
  | BEGINPROOF
  | BEGINNAME of (string)
  | BEGINHEADER
  | ENDPROOF
  | EOF

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> string * (Phrase.phrase * bool) list
