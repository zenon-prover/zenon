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

open Parsing;;
# 4 "parsezen.mly"
Version.add "$Id: parsezen.mly,v 1.16 2012-04-11 18:27:26 doligez Exp $";;

open Printf;;

open Expr;;
open Namespace;;
open Phrase;;

let rec myfold f e el =
  match el with
  | [] -> e
  | h::t -> f (e, myfold f h t)
;;

let mkand e el = myfold eand e el;;
let mkor e el = myfold eor e el;;
let mkimply e el = myfold eimply e el;;
let mkequiv e el = myfold eequiv e el;;
let mkrimply e el = myfold (fun (a, b) -> eimply (b, a)) e el;;

let mk_eall (vars, typ, body) =
  let f v b = eall (evar v, typ, b) in
  List.fold_right f vars body
;;

let mk_eex (vars, typ, body) =
  let f v b = eex (evar v, typ, b) in
  List.fold_right f vars body
;;

let mk_elam (vars, typ, body) =
  let f v b = elam (evar v, typ, b) in
  List.fold_right f vars body
;;

let mk_pattern constr vars body =
  mk_elam (vars, "", eapp ("$match-case", [evar constr; body]))
;;

let hyp_counter = ref 0;;
let gen_hyp_name () =
  incr hyp_counter;
  sprintf "%s%d" anon_prefix !hyp_counter
;;

let mk_string s = evar ("\"" ^ s ^ "\"");;

# 84 "parsezen.ml"
let yytransl_const = [|
  257 (* OPEN *);
  258 (* CLOSE *);
    0 (* EOF *);
  262 (* ALL *);
  263 (* AND *);
  264 (* DEF *);
  265 (* EQUAL *);
  266 (* EQUIV *);
  267 (* EX *);
  268 (* FALSE *);
  269 (* FIX *);
  270 (* FIXPOINT *);
  271 (* GOAL *);
  272 (* HYP *);
  273 (* IMPLY *);
  274 (* INCLUDE *);
  275 (* INDSET *);
  276 (* INDPROP *);
  277 (* LAMBDA *);
  278 (* LET *);
  279 (* MATCH *);
  280 (* NOT *);
  281 (* OR *);
  282 (* RIMPLY *);
  283 (* SELF *);
  284 (* SIG *);
  285 (* TAU *);
  286 (* TRUE *);
    0|]

let yytransl_block = [|
  259 (* IDENT *);
  260 (* STRING *);
  261 (* INT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\009\000\009\000\
\011\000\011\000\010\000\010\000\004\000\004\000\006\000\006\000\
\003\000\007\000\007\000\012\000\012\000\013\000\013\000\008\000\
\008\000\014\000\014\000\014\000\000\000"

let yylen = "\002\000\
\001\000\002\000\007\000\008\000\004\000\002\000\006\000\008\000\
\002\000\001\000\001\000\004\000\004\000\005\000\005\000\005\000\
\005\000\005\000\003\000\001\000\003\000\001\000\004\000\004\000\
\001\000\004\000\005\000\005\000\004\000\005\000\002\000\000\000\
\007\000\006\000\007\000\006\000\000\000\002\000\000\000\001\000\
\001\000\000\000\002\000\000\000\006\000\001\000\003\000\000\000\
\005\000\000\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\053\000\000\000\041\000\000\000\000\000\000\000\
\010\000\011\000\022\000\020\000\006\000\025\000\040\000\000\000\
\009\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\021\000\000\000\
\000\000\000\000\046\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\019\000\005\000\000\000\000\000\000\000\000\000\
\000\000\038\000\000\000\000\000\031\000\012\000\023\000\000\000\
\000\000\000\000\024\000\000\000\000\000\000\000\029\000\000\000\
\000\000\013\000\000\000\000\000\000\000\026\000\000\000\043\000\
\000\000\000\000\000\000\000\000\000\000\014\000\027\000\018\000\
\030\000\016\000\047\000\000\000\028\000\015\000\017\000\000\000\
\000\000\007\000\003\000\000\000\036\000\000\000\000\000\000\000\
\000\000\000\000\000\000\004\000\035\000\000\000\000\000\000\000\
\000\000\008\000\000\000\034\000\000\000\000\000\000\000\000\000\
\045\000\033\000\051\000\052\000\000\000\049\000"

let yydgoto = "\002\000\
\011\000\012\000\014\000\054\000\055\000\024\000\079\000\131\000\
\056\000\022\000\074\000\097\000\068\000\144\000"

let yysindex = "\010\000\
\001\000\000\000\000\000\016\255\016\255\001\255\019\255\017\255\
\024\255\030\255\000\000\001\000\000\000\044\255\045\255\040\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\016\255\
\000\000\066\255\067\255\000\000\052\255\070\255\069\255\001\255\
\072\255\001\255\001\255\001\255\072\255\074\255\072\255\001\255\
\014\255\001\255\001\255\001\255\001\255\078\255\079\255\001\255\
\069\255\081\255\069\255\083\255\069\255\012\255\001\255\080\255\
\086\255\087\255\001\255\001\255\001\255\090\255\000\000\001\255\
\001\255\001\255\000\000\091\255\093\255\094\255\001\255\001\255\
\096\255\097\255\000\000\000\000\099\255\081\255\100\255\102\255\
\069\255\000\000\001\255\103\255\000\000\000\000\000\000\104\255\
\105\255\106\255\000\000\107\255\108\255\014\255\000\000\092\255\
\109\255\000\000\110\255\111\255\095\255\000\000\113\255\000\000\
\112\255\001\255\115\255\117\255\001\255\000\000\000\000\000\000\
\000\000\000\000\000\000\069\255\000\000\000\000\000\000\054\255\
\114\255\000\000\000\000\001\255\000\000\118\255\119\255\001\255\
\121\255\122\255\124\255\000\000\000\000\001\255\125\255\001\255\
\005\255\000\000\093\255\000\000\127\255\005\255\005\255\129\255\
\000\000\000\000\000\000\000\000\114\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\128\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\057\255\131\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\132\255\133\255\132\255\000\000\057\255\000\000\131\255\000\000\
\000\000\000\000\131\255\000\000\131\255\000\000\000\000\131\255\
\131\255\134\255\000\000\000\000\135\255\000\000\131\255\131\255\
\000\000\000\000\000\000\000\000\000\000\133\255\000\000\000\000\
\132\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\132\255\000\000\000\000\000\000\000\000\
\136\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\137\255\000\000\135\255\000\000\000\000\137\255\137\255\000\000\
\000\000\000\000\000\000\000\000\136\255\000\000"

let yygindex = "\000\000\
\112\000\000\000\254\255\215\255\250\255\000\000\062\000\248\255\
\019\000\242\255\000\000\003\000\049\000\120\255"

let yytablesize = 285
let yytable = "\021\000\
\003\000\016\000\015\000\017\000\018\000\147\000\148\000\077\000\
\142\000\080\000\001\000\082\000\019\000\083\000\016\000\084\000\
\066\000\018\000\058\000\013\000\025\000\048\000\062\000\023\000\
\064\000\019\000\026\000\059\000\060\000\061\000\020\000\143\000\
\027\000\065\000\067\000\069\000\070\000\071\000\072\000\107\000\
\031\000\076\000\032\000\020\000\029\000\033\000\034\000\030\000\
\035\000\036\000\037\000\038\000\039\000\089\000\051\000\128\000\
\040\000\129\000\037\000\094\000\037\000\041\000\042\000\043\000\
\044\000\045\000\049\000\050\000\046\000\047\000\052\000\053\000\
\057\000\085\000\127\000\063\000\108\000\088\000\073\000\090\000\
\075\000\086\000\092\000\093\000\078\000\081\000\031\000\067\000\
\087\000\099\000\100\000\091\000\095\000\096\000\116\000\098\000\
\101\000\120\000\102\000\123\000\103\000\105\000\126\000\106\000\
\109\000\110\000\111\000\112\000\113\000\114\000\117\000\118\000\
\119\000\121\000\130\000\122\000\124\000\132\000\125\000\133\000\
\134\000\135\000\136\000\028\000\137\000\138\000\140\000\139\000\
\146\000\141\000\149\000\039\000\032\000\037\000\042\000\010\000\
\044\000\048\000\050\000\104\000\150\000\145\000\115\000\000\000\
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
\004\000\000\000\000\000\000\000\000\000\000\000\005\000\006\000\
\007\000\000\000\008\000\009\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\010\000"

let yycheck = "\006\000\
\000\000\001\001\005\000\003\001\004\001\142\000\143\000\049\000\
\004\001\051\000\001\000\053\000\012\001\002\001\001\001\004\001\
\003\001\004\001\033\000\004\001\004\001\024\000\037\000\005\001\
\039\000\012\001\003\001\034\000\035\000\036\000\030\001\027\001\
\003\001\040\000\041\000\042\000\043\000\044\000\045\000\081\000\
\001\001\048\000\003\001\030\001\001\001\006\001\007\001\003\001\
\009\001\010\001\011\001\012\001\013\001\060\000\003\001\002\001\
\017\001\004\001\002\001\066\000\004\001\022\001\023\001\024\001\
\025\001\026\001\001\001\001\001\029\001\030\001\001\001\003\001\
\001\001\055\000\116\000\002\001\083\000\059\000\001\001\061\000\
\002\001\002\001\064\000\065\000\004\001\003\001\001\001\094\000\
\002\001\071\000\072\000\002\001\002\001\001\001\003\001\002\001\
\001\001\003\001\002\001\106\000\002\001\002\001\109\000\002\001\
\002\001\002\001\002\001\002\001\002\001\002\001\002\001\002\001\
\002\001\001\001\001\001\004\001\002\001\124\000\002\001\002\001\
\002\001\128\000\002\001\012\000\003\001\002\001\002\001\134\000\
\002\001\136\000\002\001\004\001\002\001\002\001\002\001\002\001\
\002\001\002\001\002\001\078\000\149\000\139\000\094\000\255\255\
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
\008\001\255\255\255\255\255\255\255\255\255\255\014\001\015\001\
\016\001\255\255\018\001\019\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\028\001"

let yynames_const = "\
  OPEN\000\
  CLOSE\000\
  EOF\000\
  ALL\000\
  AND\000\
  DEF\000\
  EQUAL\000\
  EQUIV\000\
  EX\000\
  FALSE\000\
  FIX\000\
  FIXPOINT\000\
  GOAL\000\
  HYP\000\
  IMPLY\000\
  INCLUDE\000\
  INDSET\000\
  INDPROP\000\
  LAMBDA\000\
  LET\000\
  MATCH\000\
  NOT\000\
  OR\000\
  RIMPLY\000\
  SELF\000\
  SIG\000\
  TAU\000\
  TRUE\000\
  "

let yynames_block = "\
  IDENT\000\
  STRING\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 93 "parsezen.mly"
                      ( [] )
# 331 "parsezen.ml"
               : Phrase.zphrase list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'phrase) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Phrase.zphrase list) in
    Obj.repr(
# 94 "parsezen.mly"
                      ( _1 :: _2 )
# 339 "parsezen.ml"
               : Phrase.zphrase list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'hyp_name) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'ident_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parsezen.mly"
      ( let idl = List.map evar _5 in Zdef (DefReal (_2, _4, idl, _7, None)) )
# 349 "parsezen.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'hyp_name) in
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'ident_list) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 101 "parsezen.mly"
      ( let idl = List.map evar _6 in
        Zdef (DefReal (_2, _5, idl, _8, Some _3))
      )
# 362 "parsezen.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'int_opt) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'hyp_name) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parsezen.mly"
      ( Zhyp (_3, _4, _2) )
# 371 "parsezen.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parsezen.mly"
      ( Zhyp (goal_name, enot _2, 0) )
# 378 "parsezen.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'string_list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 109 "parsezen.mly"
      ( Zsig (_2, _4, _6) )
# 387 "parsezen.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'ident_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'constr_list) in
    Obj.repr(
# 111 "parsezen.mly"
      ( Zinductive (_2, _4, _7, _2 ^ "_ind") )
# 396 "parsezen.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 113 "parsezen.mly"
      ( Zinclude (_2) )
# 403 "parsezen.ml"
               : 'phrase))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 117 "parsezen.mly"
                                         ( evar _1 )
# 410 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 118 "parsezen.mly"
                                         ( eapp ("$string", [mk_string _1]) )
# 417 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 119 "parsezen.mly"
                                         ( eapp (_2, _3) )
# 425 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 120 "parsezen.mly"
                                         ( enot (_3) )
# 432 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 121 "parsezen.mly"
                                         ( mkand _3 _4 )
# 440 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 122 "parsezen.mly"
                                         ( mkor _3 _4 )
# 448 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 123 "parsezen.mly"
                                         ( mkimply _3 _4 )
# 456 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 124 "parsezen.mly"
                                         ( mkrimply _3 _4 )
# 464 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 125 "parsezen.mly"
                                         ( mkequiv _3 _4 )
# 472 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 126 "parsezen.mly"
                                         ( etrue )
# 478 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 127 "parsezen.mly"
                                         ( etrue )
# 484 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 128 "parsezen.mly"
                                         ( efalse )
# 490 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 129 "parsezen.mly"
                                         ( efalse )
# 496 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'mlambda) in
    Obj.repr(
# 130 "parsezen.mly"
                                         ( mk_eall _3 )
# 503 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'mlambda) in
    Obj.repr(
# 131 "parsezen.mly"
                                         ( mk_eex _3 )
# 510 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'mlambda) in
    Obj.repr(
# 132 "parsezen.mly"
                                         ( mk_elam _1 )
# 517 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'lambda) in
    Obj.repr(
# 133 "parsezen.mly"
                                         ( etau _3 )
# 524 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 134 "parsezen.mly"
                                         ( eapp ("=", [_3; _4]) )
# 532 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'case_list) in
    Obj.repr(
# 135 "parsezen.mly"
                                         ( eapp ("$match", _3 :: _4) )
# 540 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'id_expr_list_expr) in
    Obj.repr(
# 136 "parsezen.mly"
                                         ( eapp ("$let", _3) )
# 547 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'mlambda) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 137 "parsezen.mly"
                                         ( eapp ("$fix", mk_elam _3 :: _4) )
# 555 "parsezen.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 141 "parsezen.mly"
                       ( _1 :: _2 )
# 563 "parsezen.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 142 "parsezen.mly"
                       ( [] )
# 569 "parsezen.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 146 "parsezen.mly"
                                                 ( (evar _3, _4, _6) )
# 578 "parsezen.ml"
               : 'lambda))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 147 "parsezen.mly"
                                                 ( (evar _3, univ_name, _5) )
# 586 "parsezen.ml"
               : 'lambda))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'ident_list) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 151 "parsezen.mly"
                                                 ( (_3, _4, _6) )
# 595 "parsezen.ml"
               : 'mlambda))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'ident_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 152 "parsezen.mly"
                                                 ( (_3, univ_name, _5) )
# 603 "parsezen.ml"
               : 'mlambda))
; (fun __caml_parser_env ->
    Obj.repr(
# 156 "parsezen.mly"
                      ( [] )
# 609 "parsezen.ml"
               : 'ident_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ident_list) in
    Obj.repr(
# 157 "parsezen.mly"
                      ( _1 :: _2 )
# 617 "parsezen.ml"
               : 'ident_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 161 "parsezen.mly"
                      ( 1 )
# 623 "parsezen.ml"
               : 'int_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 162 "parsezen.mly"
                      ( _1 )
# 630 "parsezen.ml"
               : 'int_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 166 "parsezen.mly"
                      ( _1 )
# 637 "parsezen.ml"
               : 'hyp_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 170 "parsezen.mly"
                        ( [] )
# 643 "parsezen.ml"
               : 'string_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'string_list) in
    Obj.repr(
# 171 "parsezen.mly"
                        ( _1 :: _2 )
# 651 "parsezen.ml"
               : 'string_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 176 "parsezen.mly"
      ( [] )
# 657 "parsezen.ml"
               : 'case_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'ident_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'case_list) in
    Obj.repr(
# 178 "parsezen.mly"
      ( mk_pattern _2 _3 _5 :: _6 )
# 667 "parsezen.ml"
               : 'case_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 183 "parsezen.mly"
      ( [_1] )
# 674 "parsezen.ml"
               : 'id_expr_list_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'id_expr_list_expr) in
    Obj.repr(
# 185 "parsezen.mly"
      ( match _3 with
        | [] -> assert false
        | body :: vals -> elam (evar (_1), "", body) :: _2 :: vals
      )
# 686 "parsezen.ml"
               : 'id_expr_list_expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 193 "parsezen.mly"
      ( [] )
# 692 "parsezen.ml"
               : 'constr_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'string_or_self_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'constr_list) in
    Obj.repr(
# 195 "parsezen.mly"
      ( (_2, _3) :: _5 )
# 701 "parsezen.ml"
               : 'constr_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 199 "parsezen.mly"
                                ( [] )
# 707 "parsezen.ml"
               : 'string_or_self_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_self_list) in
    Obj.repr(
# 200 "parsezen.mly"
                                ( Param _1 :: _2 )
# 715 "parsezen.ml"
               : 'string_or_self_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_self_list) in
    Obj.repr(
# 201 "parsezen.mly"
                                ( Self :: _2 )
# 722 "parsezen.ml"
               : 'string_or_self_list))
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
   (Parsing.yyparse yytables 1 lexfun lexbuf : Phrase.zphrase list)
;;
