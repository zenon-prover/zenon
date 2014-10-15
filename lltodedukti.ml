open Printf
open Expr
open Llproof
open Namespace
open Lltolj

module Dk = Dkterm

let new_name =
  let r = ref 0 in
  fun () ->
    let n = !r in
    incr r;
    n

let new_hypo () = sprintf "H%d" (new_name ())

let new_prop () = sprintf "P%d" (new_name ())

let new_term () = sprintf "X%d" (new_name ())

let rec p_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args ->
    fprintf oc "%a %a"
      printer a (p_list printer) args

let rec p_comma_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args ->
    fprintf oc "%a, %a"
      printer a (p_comma_list printer) args

let rec p_single_arrow_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args ->
    fprintf oc "%a -> %a"
      printer a (p_single_arrow_list printer) args

let rec p_double_arrow_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args ->
    fprintf oc "%a => %a"
      printer a (p_double_arrow_list printer) args

let p_var oc e =
match e with
| Evar(s, _) -> fprintf oc "%s" s;
| _ -> assert false

let rec p_chars oc s =
  let n = Char.code (String.get s 0) in
  if not ((64 < n && n < 91)||(96 < n && n < 123))
  then fprintf oc "V";
  String.iter (fprintf oc "%a" p_char) s

and p_char oc c =
  let n = Char.code c in
  if (47 < n && n < 58) ||(64 < n && n < 91)
    ||(96 < n && n < 123) || (n = 95)
  then fprintf oc "%c" c
  else fprintf oc "%d" n

let rec trexpr e =
  match e with
  | Eand (Eimply (e1, e2, _), Eimply (e3, e4, _), _)
    when (equal e3 e2 && equal e4 e1) -> Dk.dkequiv (trexpr e1) (trexpr e2)
  | Enot (Enot (Enot (Enot (Enot (e, _), _), _), _), _) ->
    Dk.dknotc (trexpr e)
  | Enot (Enot ( Eand (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkandc (trexpr e1) (trexpr e2)
  | Enot (Enot ( Eor (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkorc (trexpr e1) (trexpr e2)
  | Enot (Enot ( Eimply (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkimplyc (trexpr e1) (trexpr e2)
  | Enot (Enot (Etrue, _), _) -> Dk.dktruec
  | Enot (Enot (Efalse, _), _) -> Dk.dkfalsec
  | Enot (Enot (
    Eall (e1, s, Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkforallc (trexpr e1) (trexpr e2)
  | Enot (Enot (
    Eex (e1, s, Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkexistsc (trexpr e1) (trexpr e2)
  | Enot (Enot (Eapp ("=", [e1;e2], _), _), _) ->
    Dk.dkeqc (trexpr e1) (trexpr e2)
  | Evar (v, _) when Mltoll.is_meta v ->
    Dk.dkanyterm
  | Evar (v, _) ->
    Dk.dkvar v
  | Eapp ("$string", [e], _) ->
    begin match e with Evar (v, _) -> Dk.dkvar ("S"^v) | _ -> assert false end
  | Eapp ("=", [e1;e2], _) ->
    Dk.dkeq (trexpr e1) (trexpr e2)
  | Eapp (s, args, _) ->
    Dk.dkapp (Dk.dkvar s) (List.map trexpr args)
  | Enot (e, _) ->
    Dk.dknot (trexpr e)
  | Eand (e1, e2, _) ->
    Dk.dkand (trexpr e1) (trexpr e2)
  | Eor (e1, e2, _) ->
    Dk.dkor (trexpr e1) (trexpr e2)
  | Eimply (e1, e2, _) ->
    Dk.dkimply (trexpr e1) (trexpr e2)
  | Etrue -> Dk.dktrue
  | Efalse -> Dk.dkfalse
  | Eall (e1, s, e2, _) ->
    Dk.dkforall (trexpr e1) (trexpr e2)
  | Eex (e1, s, e2, _) ->
    Dk.dkexists (trexpr e1) (trexpr e2)
  | Elam _ | Eequiv _ | Emeta _ | Etau _ -> assert false

let rec p_expr oc e =
  Dk.p_term_p oc (trexpr e)

let p_prf oc e =
  fprintf oc "logic.prf %a" p_expr e

let p_declare oc (e, printer) =
  fprintf oc "%t : %a" printer p_expr e

let p_declare_prf oc (e, printer) =
  fprintf oc "%t : %a" printer p_prf e

let p_str s oc =
  fprintf oc "%s" s

(* the left part of sequents can only grow: the left part of the conclusion is always contained in the left part of the hypothesis
weakening is implicit*)

let rec p_proof oc (lkproof, goal, gamma) =
  let poc fmt = fprintf oc fmt in
  let g, d, lkrule = lkproof in
  let p_hyp oc e =
    try (List.assoc e gamma) oc
    with Not_found -> fprintf oc "axiom error" in
  match lkrule with
  | SCaxiom (e) ->
    poc "%a" p_hyp e
  | SCfalse ->
    poc "(%a %a)" p_hyp efalse p_expr goal
  | SCtrue ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(%s : logic.Prop => %s : logic.prf %s => %s)"
      prop var prop var
  | SCeqref (a) ->
    let prop = new_prop () in
    poc "(%s : (logic.Term -> logic.Prop) => %a)"
      prop p_proof (
	scrimply (
	  eapp (prop, [a]),
	  eapp (prop, [a]),
	  scaxiom (eapp (prop, [a]), [])),
	eimply (eapp (prop, [a]), eapp (prop, [a])), gamma)
  | SCeqsym (a, b) ->
    let term = new_term () in
    poc "(%a (%s:logic.Term => %a) %a)"
      p_hyp (eapp ("=", [a; b]))
      term p_expr (eapp ("=", [evar term; a]))
      p_proof (sceqref (a, []), eapp ("=", [a; a]), gamma)
  | SCcut (e, lkrule1, lkrule2) ->
    poc "%a" p_proof
      (lkrule2, goal,
       (e, fun oc -> p_proof oc (lkrule1, e, gamma)) :: gamma)
  | SCland (e1, e2, lkrule) ->
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%a %a (%a => %a => %a))"
      p_hyp (eand (e1, e2))
      p_expr goal
      p_declare_prf (e1, p_str var1) p_declare_prf (e2, p_str var2)
      p_proof (lkrule, goal, (e1, p_str var1) :: (e2, p_str var2) :: gamma)
  | SClor (e1, e2, lkrule1, lkrule2) ->
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%a %a (%a => %a) (%a => %a))"
      p_hyp (eor (e1, e2))
      p_expr goal
      p_declare_prf (e1, p_str var1)
      p_proof (lkrule1, goal, (e1, p_str var1) :: gamma)
      p_declare_prf (e2, p_str var2)
      p_proof (lkrule2, goal, (e2, p_str var2) :: gamma)
  | SClimply (e1, e2, lkrule1, lkrule2) ->
    let p_aux oc =
      fprintf oc "(%a %a)"
	p_hyp (eimply (e1, e2))
	p_proof (lkrule1, e1, gamma) in
    poc "%a"
      p_proof (lkrule2, goal, (e2, p_aux) :: gamma)
  | SClnot (e, lkrule) ->
    poc "(%a %a)" p_hyp (enot e) p_proof (lkrule, e, gamma)
  | SClall (Eall (x, ty, p, _) as ap, t, lkrule) ->
    let p_aux oc =
      fprintf oc "(%a %a)"
	p_hyp ap p_expr t in
    poc "%a"
      p_proof
      (lkrule, goal, (substitute [(x, t)] p, p_aux) :: gamma)
  | SClex (Eex (x, ty, p, _) as ep, v, lkrule) ->
    let q = substitute [(x, v)] p in
    let var = new_hypo () in
    poc "(%a %a (%a:logic.Term => %s:logic.prf %a => %a))"
      p_hyp ep p_expr goal
      p_expr v var p_expr q
      p_proof
      (lkrule, goal, (q, p_str var) :: gamma)
  | SCrand (e1, e2, lkrule1, lkrule2) ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(%s : logic.Prop => %s : (%a -> %a -> logic.prf %s) => %s %a %a)"
      prop var
      p_prf e1 p_prf e2 prop
      var p_proof (lkrule1, e1, gamma) p_proof (lkrule2, e2, gamma)
  | SCrorl (e1, e2, lkrule) ->
    let prop = new_prop () in
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%s : logic.Prop => %s : (%a -> logic.prf %s) => %s : (%a -> logic.prf %s) => %s %a)"
      prop var1 p_prf e1 prop var2 p_prf e2 prop
      var1 p_proof (lkrule, e1, gamma)
  | SCrorr (e1, e2, lkrule) ->
    let prop = new_prop () in
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%s : logic.Prop => %s : (%a -> logic.prf %s) => %s : (%a -> logic.prf %s) => %s %a)"
      prop var1 p_prf e1 prop var2 p_prf e2 prop
      var2 p_proof (lkrule, e2, gamma)
  | SCrimply (e1, e2, lkrule) ->
    let var = new_hypo () in
    poc "(%s : %a => %a)"
      var p_prf e1 p_proof (lkrule, e2, (e1, p_str var) :: gamma)
  | SCrnot (e, lkrule) ->
    let var = new_hypo () in
    poc "(%a => %a)" p_declare_prf (e, p_str var)
      p_proof (lkrule, efalse, (e, p_str var) :: gamma)
  | SCrall (Eall (x, ty, p, _), v, lkrule) ->
    let q = substitute [(x, v)] p in
    poc "(%a:logic.Term => %a)"
      p_expr v p_proof
      (lkrule, q, gamma)
  | SCrex (Eex (x, ty, p, _), t, lkrule) ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(%s:logic.Prop => %s: (%a:logic.Term -> logic.prf %a -> logic.prf %s) => %s %a %a)"
      prop var
      p_expr x p_expr p prop
      var p_expr t
      p_proof (lkrule, substitute [(x, t)] p, gamma)
  | SCcnot (e, lkrule) ->
    poc "proof must be constructive"
  | SClcontr (e, lkrule) ->
    poc "%a"
      p_proof (lkrule, goal, gamma)
  | SCrweak (e, lkrule) ->
    poc "(%a %a)"
      p_proof (lkrule, efalse, gamma)
      p_expr e
  | SCeqfunc (Eapp (p, ts, _), Eapp (_, us, _)) ->
    let pred = new_prop () in
    let var = new_hypo () in
    let rec itereq oc (xts, ts, us) =
      match ts, us with
      | [], [] -> fprintf oc "%s" var
      | t :: ts, u :: us ->
	(*let var1 = new_hypo () in
	  let var2 = new_hypo () in*)
	let term = new_term () in
	poc "(%a (%s:logic.Term => %a) %a)"
	  p_hyp (eapp ("=", [t; u]))
	  term p_expr
	  (eapp (pred, [eapp (p, xts @ ((evar term) :: us))]))
	  itereq ((xts@[t]), ts, us)
      | _ -> assert false;
    in
    poc "(%s:(logic.Term -> logic.Prop) => %s:logic.prf %a => %a)"
      pred var p_expr (eapp (pred, [eapp (p, ts)]))
      itereq ([], ts, us)
  | SCeqprop (Eapp (p, ts, _), Eapp (_, us, _)) ->
    let rec itereq oc (xts, ts, us) =
      match ts, us with
      | [], [] -> fprintf oc "%a" p_hyp (eapp (p, xts))
      | t :: ts, u :: us ->
	let term = new_term () in
	poc "(%a (%s:logic.Term => %a) %a)"
	  p_hyp (eapp ("=", [t; u]))
	  term p_expr (eapp (p, xts @ ((evar term) :: us)))
	  itereq ((xts@[t]), ts, us)
      | _ -> assert false;
    in
    poc "%a" itereq ([], ts, us)
  | _ -> assert false

let rec p_tree oc proof goal =
  let ljproof = lltolj proof goal in
  let conc = scconc ljproof in
  fprintf oc "conjecture_proof : %a :=\n"
    p_prf conc;
  fprintf oc "%a."
    p_proof (ljproof, conc, [])

let rec get_goal phrases =
  match phrases with
  | [] -> None
  | Phrase.Hyp (name, e, _) :: _ when name = goal_name -> Some e
  | _ :: t -> get_goal t

let p_theorem oc phrases l =
  match l with
  | [] -> assert false
  | thm :: lemmas ->
    List.iter
      (fun lemma ->
	Hashtbl.add Lltolj.lemma_env lemma.name lemma.proof)
      lemmas;
    let goal = get_goal phrases in
    p_tree oc thm.proof goal

type result =
  | Prop
  | Term
  | Indirect of string

type signature =
  | Default of int * result

let predefined = ["="; "$string"]

let rec get_signatures ps =
  let symtbl = (Hashtbl.create 97 : (string, signature) Hashtbl.t) in
  let add_sig sym arity kind =
    if not (Hashtbl.mem symtbl sym) then
      Hashtbl.add symtbl sym (Default (arity, kind))
  in
  let rec get_sig r env e =
    match e with
    | Evar (s, _) -> if not (List.mem s env) then add_sig s 0 r;
    | Emeta  _ | Etrue | Efalse -> ()
    | Eapp ("$string", [Evar (s, _)], _) ->
      (if not (List.mem_assoc e !Lltolj.distinct_terms)
       then
	  Lltolj.distinct_terms :=
	    (e, (List.length !Lltolj.distinct_terms) + 1)
	  :: !Lltolj.distinct_terms; add_sig ("S"^s) 0 Term)
    | Eapp (s, args, _) ->
        add_sig s (List.length args) r;
	List.iter (get_sig Term env) args;
    | Eand (e1, e2, _) | Eor (e1, e2, _)
    | Eimply (e1, e2, _) | Eequiv (e1, e2, _)
      -> get_sig Prop env e1;
	 get_sig Prop env e2;
    | Enot (e1, _) -> get_sig Prop env e1;
    | Eall (Evar (v, _), _, e1, _) | Eex (Evar (v, _), _, e1, _)
      -> get_sig Prop (v::env) e1;
    | Eex _ | Eall _ | Etau _ | Elam _ -> assert false
  in
  let do_phrase p =
    match p with
      | Phrase.Hyp (name, e, _) ->
	get_sig Prop [] e;
      | Phrase.Def (DefReal ("", s, _, e, None)) ->
	get_sig (Indirect s) [] e;
      | _ -> assert false
  in
  List.iter do_phrase ps;
  let rec follow_indirect path s =
    if List.mem s path then Prop else
      begin try
        match Hashtbl.find symtbl s with
	| Default (_, ((Prop|Term) as kind)) -> kind
	| Default (_, Indirect s1) -> follow_indirect (s::path) s1
      with Not_found -> Prop
      end
  in
  let find_sig sym sign l =
    if List.mem sym predefined then l
    else begin
      match sign with
      | Default (arity, (Prop|Term)) -> (sym, sign) :: l
      | Default (arity, Indirect s) ->
          (sym, Default (arity, follow_indirect [] s)) :: l
    end
  in
  Hashtbl.fold find_sig symtbl []

let p_signature oc (sym, sign) =
  let rec p_arity n =
    if n = 0 then () else begin
      fprintf oc "logic.Term -> ";
      p_arity (n-1);
    end;
  in
  fprintf oc "%a : " p_expr (evar sym);
  match sign with
  | Default (arity, kind) ->
      begin
        p_arity arity;
        match kind with
        | Prop -> fprintf oc "logic.Prop.\n";
        | Term -> fprintf oc "logic.Term.\n";
        | _ -> assert false;
      end

let declare_hyp oc h =
  match h with
  | Phrase.Hyp (name, _, _) when name = goal_name -> ()
  | Phrase.Hyp (name, stmt, _) ->
    Lltolj.hypothesis_env :=
      stmt :: !Lltolj.hypothesis_env;
  | Phrase.Def (DefReal ("", sym, params, body, None)) ->
    Hashtbl.add Lltolj.definition_env
      sym (params, body);
    fprintf oc "[%a] " (p_comma_list p_var) params;
    fprintf oc "%s %a " sym (p_list p_var) params;
    fprintf oc "--> %a.\n" p_expr body;
  | _ -> assert false

let rec add_distinct_terms_axioms l =
  match l with
  | (x, n) :: (y, m) :: l ->
    Lltolj.hypothesis_env :=
      enot (eapp ("=", [y; x])) :: !Lltolj.hypothesis_env;
    add_distinct_terms_axioms ((x, n) :: l);
    add_distinct_terms_axioms ((y, m) :: l);
  | _ -> ()

let timeout = ref 10

let output oc phrases ppphrases llp filename =
  Lltolj.hypothesis_env := [];
  let name =
    let buf = Buffer.create (2*String.length filename) in
    String.iter
      (fun c -> match c with
      | 'a'..'z' | 'A'..'Z' | '0'..'9' -> Buffer.add_char buf c
      | '_' -> Buffer.add_string buf "__"
      | _ -> Buffer.add_string buf ("_"^(string_of_int (int_of_char c)))) filename;
    Buffer.add_string buf "todk";
    Buffer.contents buf in
  Dk.p_line oc (Dk.dkprelude name);
  let sigs = get_signatures phrases in
  List.iter (p_signature oc) sigs;
  List.iter (declare_hyp oc) phrases;
  add_distinct_terms_axioms !Lltolj.distinct_terms;
  p_theorem oc phrases (List.rev llp)

let outputterm oc phrases ppphrases llp =
  Lltolj.hypothesis_env := [];
  add_distinct_terms_axioms !Lltolj.distinct_terms;
  p_theorem oc phrases (List.rev llp)
