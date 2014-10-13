open Printf

type dkvar = string

type dkterm = 
  | Dkvar of dkvar
  | Dklam of dkterm * dkterm * dkterm
  | Dkapp of dkterm list
  | Dkarrow of dkterm * dkterm
  | Dktermtype
  | Dkproptype
  | Dknot
  | Dkand
  | Dkimply
  | Dkfalse
  | Dkeq
  | Dkprf

type dkline =
  | Dkdecl of dkterm * dkterm
  | Dkdeftype of dkterm * dkterm * dkterm
  | Dkprelude of string

let mk_var var = Dkvar var
let mk_lam var t term = Dklam (var, t, term)
let mk_lams vars types e = 
  List.fold_left2 (fun term var t -> mk_lam var t term) e (List.rev vars) (List.rev types)

let mk_app t ts = Dkapp (t :: ts)
let mk_app2 t1 t2 = mk_app t1 [t2]
let mk_app3 t1 t2 t3 = mk_app t1 [t2; t3]
let mk_arrow t1 t2 = Dkarrow (t1, t2)
let mk_termtype = Dktermtype
let mk_proptype = Dkproptype
let mk_not term = mk_app2 Dknot term
let mk_and p q = mk_app3 Dkand p q
let mk_imply p q = mk_app3 Dkimply p q
let mk_false = Dkfalse
let mk_eq t1 t2 = mk_app3 Dkeq t1 t2
let mk_prf t = mk_app2 Dkprf t

let mk_decl t term = Dkdecl (t, term)
let mk_deftype t termtype term = Dkdeftype (t, termtype, term)
let mk_prelude name = Dkprelude (name)

let p_var out var = fprintf out "%s" var

let rec p_term out term =
  match term with
  | Dkvar (var) -> p_var out var
  | Dklam (t, t1, t2) -> 
    fprintf out "%a: %a => %a"
      p_term t p_term_p t1 p_term_p t2
  | Dkapp (ts) -> p_terms out ts
  | Dkarrow (t1, t2) -> 
    fprintf out "%a -> %a"
      p_term_p t1 p_term_p t2
  | Dktermtype -> fprintf out "logic.Term"
  | Dkproptype -> fprintf out "logic.Prop"
  | Dknot -> fprintf out "logic.not"
  | Dkand -> fprintf out "logic.and"
  | Dkimply -> fprintf out "logic.imply"
  | Dkfalse -> fprintf out "logic.False"
  | Dkeq -> fprintf out "logic.equal"
  | Dkprf -> fprintf out "logic.prf"

and p_term_p out term = 
  match term with
  | Dklam _ | Dkapp _ | Dkarrow _ ->
    fprintf out "(%a)" p_term term
  | _ -> p_term out term

and p_terms out terms = 
  match terms with
  | [] -> ()
  | [t] -> p_term_p out t
  | t :: q -> 
    fprintf out "%a %a"
      p_term_p t p_terms q

let p_line out line =
  match line with
  | Dkdecl (t, term) -> 
    fprintf out "%a: %a.\n"
      p_term t
      p_term term
  | Dkdeftype (t, typeterm, term) ->
    fprintf out "%a: %a:= %a.\n"
      p_term t
      p_term typeterm
      p_term term
  | Dkprelude (name) -> fprintf out "#NAME %s.\n" name;
