open Printf

type dkvar = string

type dkterm = 
  | Dkvar of dkvar
  | Dklam of dkterm * dkterm * dkterm
  | Dkpi of dkterm * dkterm * dkterm
  | Dkapp of dkterm list
  | Dkarrow of dkterm * dkterm
  | Dkprf
  | Dktermtype
  | Dkproptype
  | Dkanyterm
  | Dknot
  | Dkand
  | Dkor
  | Dkimply
  | Dkforall
  | Dkexists
  | Dktrue
  | Dkfalse
  | Dkeq
  | Dknotc
  | Dkandc
  | Dkorc
  | Dkimplyc
  | Dkforallc
  | Dkexistsc
  | Dktruec
  | Dkfalsec
  | Dkeqc
  | Dkequiv 

type dkline =
  | Dkdecl of dkterm * dkterm
  | Dkdeftype of dkterm * dkterm * dkterm
  | Dkprelude of string
  | Dkrewrite of (dkterm * dkterm) list * dkterm * dkterm

let dkvar var = Dkvar var
let dklam var t term = Dklam (var, t, term)
let dklams vars types e = 
  List.fold_left2 (fun term var t -> dklam var t term) e (List.rev vars) (List.rev types)
let dkpi var t term = Dkpi (var, t, term)
let dkapp t ts = Dkapp (t :: ts)
let dkapp2 t1 t2 = dkapp t1 [t2]
let dkapp3 t1 t2 t3 = dkapp t1 [t2; t3]
let dkarrow t1 t2 = Dkarrow (t1, t2)
let dkprf t = dkapp2 Dkprf t
let dktermtype = Dktermtype
let dkproptype = Dkproptype
let dkanyterm = Dkanyterm
let dknot term = dkapp2 Dknot term
let dkand p q = dkapp3 Dkand p q
let dkor p q = dkapp3 Dkor p q
let dkimply p q = dkapp3 Dkimply p q
let dkforall x p = dkapp2 Dkforall (dklam x dktermtype p)
let dkexists x p = dkapp2 Dkexists (dklam x dktermtype p)
let dktrue = Dktrue
let dkfalse = Dkfalse
let dkeq t1 t2 = dkapp3 Dkeq t1 t2
let dknotc term = dkapp2 Dknotc term
let dkandc p q = dkapp3 Dkandc p q
let dkorc p q = dkapp3 Dkorc p q
let dkimplyc p q = dkapp3 Dkimplyc p q
let dkforallc x p = dkapp2 Dkforallc (dklam x dktermtype p)
let dkexistsc x p = dkapp2 Dkexistsc (dklam x dktermtype p)
let dktruec = Dktruec
let dkfalsec = Dkfalsec
let dkeqc t1 t2 = dkapp3 Dkeqc t1 t2
let dkequiv p q = dkapp3 Dkequiv p q

let dkdecl t term = Dkdecl (t, term)
let dkdeftype t termtype term = Dkdeftype (t, termtype, term)
let dkprelude name = Dkprelude (name)
let dkrewrite env t1 t2 = Dkrewrite (env, t1, t2)

let p_var out var = fprintf out "%s" var

let rec p_term out term =
  match term with
  | Dkvar (var) -> p_var out var
  | Dklam (var, t, term) -> 
    fprintf out "%a: %a => %a"
      p_term var p_term_p t p_term_p term
  | Dkpi (var, t, term) ->     
    fprintf out "%a: %a -> %a"
      p_term var p_term_p t p_term_p term
  | Dkapp (ts) -> p_terms out ts
  | Dkarrow (t1, t2) -> 
    fprintf out "%a -> %a"
      p_term_p t1 p_term_p t2
  | Dkprf -> fprintf out "logic.prf"
  | Dktermtype -> fprintf out "logic.Term"
  | Dkproptype -> fprintf out "logic.Prop"
  | Dkanyterm -> fprintf out "logic.anyterm"
  | Dknot -> fprintf out "logic.not"
  | Dkand -> fprintf out "logic.and"
  | Dkor -> fprintf out "logic.or"
  | Dkimply -> fprintf out "logic.imply"
  | Dkforall -> fprintf out "logic.forall"
  | Dkexists -> fprintf out "logic.exists"
  | Dktrue -> fprintf out "logic.True"
  | Dkfalse -> fprintf out "logic.False"
  | Dkeq -> fprintf out "logic.equal"
  | Dknotc -> fprintf out "logic.noc"
  | Dkandc -> fprintf out "logic.andc"
  | Dkorc -> fprintf out "logic.orc"
  | Dkimplyc -> fprintf out "logic.implyc"
  | Dkforallc -> fprintf out "logic.forallc"
  | Dkexistsc -> fprintf out "logic.existsc"
  | Dktruec -> fprintf out "logic.Truec"
  | Dkfalsec -> fprintf out "logic.Falsec"
  | Dkeqc -> fprintf out "logic.equalc"
  | Dkequiv -> fprintf out "logic.equiv"

and p_term_p out term = 
  match term with
  | Dklam _ | Dkpi _ | Dkapp _ | Dkarrow _ ->
    fprintf out "(%a)" p_term term
  | _ -> p_term out term

and p_terms out terms = 
  match terms with
  | [] -> ()
  | [t] -> p_term_p out t
  | t :: q -> 
    fprintf out "%a %a"
      p_term_p t p_terms q

let p_env out env =
  let p_type out (x, t) =
    fprintf out "%a: %a"
      p_term x
      p_term t in
  match env with 
  | e1 :: e2 :: env ->
    fprintf out "%a, %a"
      p_type e1
      p_type e2
  | _ -> List.iter (p_type out) env

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
  | Dkprelude (name) -> fprintf out "#NAME %s.\n" name
  | Dkrewrite (env, t1, t2) ->
    fprintf out "[%a] " p_env env;
    fprintf out "%a " p_term t1;
    fprintf out "--> %a.\n" p_term t2;
