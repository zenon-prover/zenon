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

open Parsing;;
# 4 "parsetptp.mly"
Version.add "$Id: parsetptp.mly,v 1.9 2012-04-24 17:32:04 doligez Exp $";;

open Printf;;

open Expr;;
open Phrase;;

let ns pre s = (if !Globals.namespace_flag then pre else "") ^ s;;
let ns_hyp s = ns "H_" s;;
let ns_var s = ns "v_" s;;
let ns_fun s = ns "f_" s;;

let rec mk_quant q vs body =
  match vs with
  | [] -> body
  | h::t -> q (h, Namespace.univ_name, mk_quant q t body)
;;

let cnf_to_formula l =
  let l1 = List.flatten (List.map Expr.get_fv l) in
  let vs = Misc.list_unique (List.sort String.compare l1) in
  let body =
    match l with
    | [] -> assert false
    | a::l2 -> List.fold_left (fun x y -> eor (x,y)) a l2
  in
  mk_quant eall (List.map evar vs) body
;;

# 67 "parsetptp.ml"
let yytransl_const = [|
  257 (* EQUIV *);
  258 (* IMPLY *);
  259 (* RIMPLY *);
  260 (* AND *);
  261 (* OR *);
  262 (* NOT *);
  263 (* TRUE *);
  264 (* FALSE *);
  265 (* ALL *);
  266 (* EX *);
  267 (* OPEN *);
  268 (* CLOSE *);
    0 (* EOF *);
  269 (* INCLUDE *);
  270 (* DOT *);
  271 (* INPUT_CLAUSE *);
  272 (* INPUT_FORMULA *);
  273 (* LBRACKET *);
  274 (* RBRACKET *);
  278 (* POSITIVE *);
  279 (* NEGATIVE *);
  280 (* COMMA *);
  281 (* EQSYM *);
  282 (* NEQSYM *);
  283 (* COLON *);
  284 (* XOR *);
  285 (* NOR *);
  286 (* NAND *);
    0|]

let yytransl_block = [|
  275 (* LIDENT *);
  276 (* UIDENT *);
  277 (* STRING *);
  287 (* ANNOT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\002\000\006\000\
\006\000\006\000\006\000\006\000\007\000\007\000\008\000\008\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\010\000\010\000\003\000\003\000\005\000\005\000\011\000\011\000\
\000\000"

let yylen = "\002\000\
\001\000\002\000\005\000\009\000\009\000\009\000\001\000\001\000\
\002\000\001\000\003\000\003\000\003\000\000\000\003\000\001\000\
\001\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\006\000\006\000\002\000\003\000\001\000\001\000\001\000\
\003\000\001\000\003\000\001\000\003\000\001\000\001\000\003\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\001\000\000\000\000\000\000\000\007\000\041\000\
\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\030\000\
\031\000\000\000\000\000\000\000\000\000\008\000\010\000\000\000\
\000\000\039\000\000\000\000\000\000\000\000\000\035\000\000\000\
\028\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\
\000\000\029\000\037\000\000\000\000\000\006\000\011\000\012\000\
\040\000\005\000\021\000\020\000\022\000\018\000\019\000\023\000\
\024\000\025\000\000\000\000\000\000\000\000\000\013\000\033\000\
\000\000\000\000\015\000\026\000\027\000"

let yydgoto = "\002\000\
\008\000\009\000\026\000\052\000\040\000\041\000\056\000\077\000\
\046\000\072\000\043\000"

let yysindex = "\007\000\
\001\000\000\000\000\000\003\255\021\255\033\255\000\000\000\000\
\001\000\249\254\015\255\031\255\000\000\247\254\040\255\045\255\
\061\255\059\255\060\255\065\255\000\000\066\255\054\255\056\255\
\071\255\078\255\010\255\083\255\066\255\085\255\083\255\000\000\
\000\000\081\255\082\255\083\255\089\255\000\000\000\000\093\255\
\253\254\000\000\072\255\083\255\094\255\058\255\000\000\087\255\
\000\000\088\255\088\255\095\255\058\255\001\255\047\255\000\000\
\096\255\047\255\047\255\083\255\097\255\083\255\083\255\083\255\
\083\255\083\255\083\255\083\255\083\255\000\000\090\255\091\255\
\098\255\000\000\000\000\048\255\100\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\088\255\086\255\092\255\047\255\000\000\000\000\
\083\255\083\255\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\099\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\023\255\000\000\000\000\000\000\
\053\255\000\000\103\255\000\000\000\000\106\255\000\000\000\000\
\000\000\000\000\000\000\000\000\106\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\102\255\000\000\
\000\000\000\000\000\000\109\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\113\000\000\000\094\000\230\255\000\000\208\255\000\000\030\000\
\229\255\210\255\089\000"

let yytablesize = 288
let yytable = "\042\000\
\003\000\045\000\017\000\049\000\073\000\060\000\076\000\001\000\
\053\000\079\000\080\000\014\000\075\000\010\000\018\000\031\000\
\032\000\033\000\034\000\035\000\036\000\058\000\059\000\014\000\
\014\000\014\000\014\000\014\000\037\000\038\000\039\000\011\000\
\081\000\015\000\014\000\083\000\084\000\085\000\086\000\087\000\
\088\000\089\000\090\000\012\000\096\000\076\000\014\000\014\000\
\014\000\016\000\014\000\014\000\014\000\032\000\032\000\032\000\
\032\000\032\000\062\000\063\000\064\000\065\000\066\000\019\000\
\032\000\037\000\038\000\039\000\020\000\100\000\101\000\094\000\
\058\000\059\000\021\000\022\000\060\000\027\000\023\000\028\000\
\032\000\032\000\032\000\024\000\025\000\067\000\068\000\069\000\
\031\000\032\000\033\000\034\000\035\000\044\000\029\000\030\000\
\048\000\050\000\051\000\055\000\070\000\037\000\038\000\039\000\
\057\000\061\000\074\000\071\000\092\000\078\000\082\000\095\000\
\097\000\091\000\038\000\093\000\036\000\017\000\098\000\034\000\
\016\000\013\000\047\000\099\000\054\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\004\000\000\000\005\000\
\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000"

let yycheck = "\027\000\
\000\000\028\000\012\001\031\000\051\000\005\001\055\000\001\000\
\036\000\058\000\059\000\019\001\012\001\011\001\024\001\006\001\
\007\001\008\001\009\001\010\001\011\001\025\001\026\001\001\001\
\002\001\003\001\004\001\005\001\019\001\020\001\021\001\011\001\
\060\000\019\001\012\001\062\000\063\000\064\000\065\000\066\000\
\067\000\068\000\069\000\011\001\091\000\094\000\024\001\025\001\
\026\001\019\001\028\001\029\001\030\001\001\001\002\001\003\001\
\004\001\005\001\001\001\002\001\003\001\004\001\005\001\024\001\
\012\001\019\001\020\001\021\001\024\001\097\000\098\000\024\001\
\025\001\026\001\014\001\017\001\005\001\024\001\019\001\024\001\
\028\001\029\001\030\001\019\001\019\001\028\001\029\001\030\001\
\006\001\007\001\008\001\009\001\010\001\011\001\024\001\018\001\
\012\001\017\001\017\001\011\001\014\001\019\001\020\001\021\001\
\012\001\012\001\012\001\020\001\018\001\014\001\014\001\012\001\
\027\001\024\001\012\001\018\001\018\001\012\001\027\001\018\001\
\012\001\009\000\029\000\094\000\036\000\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\013\001\255\255\015\001\
\016\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\031\001"

let yynames_const = "\
  EQUIV\000\
  IMPLY\000\
  RIMPLY\000\
  AND\000\
  OR\000\
  NOT\000\
  TRUE\000\
  FALSE\000\
  ALL\000\
  EX\000\
  OPEN\000\
  CLOSE\000\
  EOF\000\
  INCLUDE\000\
  DOT\000\
  INPUT_CLAUSE\000\
  INPUT_FORMULA\000\
  LBRACKET\000\
  RBRACKET\000\
  POSITIVE\000\
  NEGATIVE\000\
  COMMA\000\
  EQSYM\000\
  NEQSYM\000\
  COLON\000\
  XOR\000\
  NOR\000\
  NAND\000\
  "

let yynames_block = "\
  LIDENT\000\
  UIDENT\000\
  STRING\000\
  ANNOT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 85 "parsetptp.mly"
                    ( [] )
# 296 "parsetptp.ml"
               : Phrase.tpphrase list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'phrase) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Phrase.tpphrase list) in
    Obj.repr(
# 86 "parsetptp.mly"
                    ( _1 :: _2 )
# 304 "parsetptp.ml"
               : Phrase.tpphrase list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 89 "parsetptp.mly"
                                   ( Phrase.Include (_3, None) )
# 311 "parsetptp.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : 'name_list) in
    Obj.repr(
# 91 "parsetptp.mly"
                                   ( Phrase.Include (_3, Some (_6)) )
# 319 "parsetptp.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    Obj.repr(
# 93 "parsetptp.mly"
                                   ( Phrase.Formula (ns_hyp _3, _5, _7) )
# 328 "parsetptp.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'cnf_formula) in
    Obj.repr(
# 95 "parsetptp.mly"
     ( Phrase.Formula (ns_hyp _3, _5, cnf_to_formula _7) )
# 337 "parsetptp.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 96 "parsetptp.mly"
                                   ( Phrase.Annotation _1 )
# 344 "parsetptp.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 99 "parsetptp.mly"
                                       ( evar (ns_var _1) )
# 351 "parsetptp.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'arguments) in
    Obj.repr(
# 100 "parsetptp.mly"
                                       ( eapp (ns_fun _1, _2) )
# 359 "parsetptp.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 101 "parsetptp.mly"
                                       ( eapp ("$string", [evar _1]) )
# 366 "parsetptp.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 102 "parsetptp.mly"
                                       ( eapp ("=", [_1; _3]) )
# 374 "parsetptp.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 103 "parsetptp.mly"
                                       ( enot (eapp ("=", [_1; _3])) )
# 382 "parsetptp.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 106 "parsetptp.mly"
                                 ( _2 )
# 389 "parsetptp.ml"
               : 'arguments))
; (fun __caml_parser_env ->
    Obj.repr(
# 107 "parsetptp.mly"
                                 ( [] )
# 395 "parsetptp.ml"
               : 'arguments))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 110 "parsetptp.mly"
                                 ( _1 :: _3 )
# 403 "parsetptp.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 111 "parsetptp.mly"
                                 ( [_1] )
# 410 "parsetptp.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 114 "parsetptp.mly"
                               ( _1 )
# 417 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 115 "parsetptp.mly"
                               ( eand (_1, _3) )
# 425 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 116 "parsetptp.mly"
                               ( eor (_1, _3) )
# 433 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 117 "parsetptp.mly"
                               ( eimply (_1, _3) )
# 441 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 118 "parsetptp.mly"
                               ( eequiv (_1, _3) )
# 449 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 119 "parsetptp.mly"
                               ( eimply (_3, _1) )
# 457 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 120 "parsetptp.mly"
                               ( enot (eequiv (_1, _3)) )
# 465 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 121 "parsetptp.mly"
                               ( enot (eor (_1, _3)) )
# 473 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 122 "parsetptp.mly"
                               ( enot (eand (_1, _3)) )
# 481 "parsetptp.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'var_list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 126 "parsetptp.mly"
                                   ( mk_quant eall _3 _6 )
# 489 "parsetptp.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'var_list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 128 "parsetptp.mly"
                                   ( mk_quant eex _3 _6 )
# 497 "parsetptp.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 129 "parsetptp.mly"
                                   ( enot (_2) )
# 504 "parsetptp.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 130 "parsetptp.mly"
                                   ( _2 )
# 511 "parsetptp.ml"
               : 'atom))
; (fun __caml_parser_env ->
    Obj.repr(
# 131 "parsetptp.mly"
                                   ( etrue )
# 517 "parsetptp.ml"
               : 'atom))
; (fun __caml_parser_env ->
    Obj.repr(
# 132 "parsetptp.mly"
                                   ( efalse )
# 523 "parsetptp.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 133 "parsetptp.mly"
                                   ( _1 )
# 530 "parsetptp.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'var_list) in
    Obj.repr(
# 136 "parsetptp.mly"
                                   ( evar (ns_var _1) :: _3 )
# 538 "parsetptp.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 137 "parsetptp.mly"
                                   ( [evar (ns_var _1)] )
# 545 "parsetptp.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'name_list) in
    Obj.repr(
# 140 "parsetptp.mly"
                                   ( _1 :: _3 )
# 553 "parsetptp.ml"
               : 'name_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 141 "parsetptp.mly"
                                   ( [_1] )
# 560 "parsetptp.ml"
               : 'name_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'disjunction) in
    Obj.repr(
# 145 "parsetptp.mly"
                                   ( _2 )
# 567 "parsetptp.ml"
               : 'cnf_formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'disjunction) in
    Obj.repr(
# 146 "parsetptp.mly"
                                   ( _1 )
# 574 "parsetptp.ml"
               : 'cnf_formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 150 "parsetptp.mly"
                                   ( [_1] )
# 581 "parsetptp.ml"
               : 'disjunction))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'disjunction) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 151 "parsetptp.mly"
                                   ( _3 :: _1 )
# 589 "parsetptp.ml"
               : 'disjunction))
(* Entry file *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let file (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Phrase.tpphrase list)
;;
