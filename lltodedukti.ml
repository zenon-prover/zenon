open Printf;;
open Expr;;
open Llproof;;
open Namespace;;
open Lltolj;;
open Rewrite;;
open Phrase;;

let new_name =
  let r = ref 0 in
  fun () ->
    let n = !r in
    incr r;
    n
;;

let new_hypo () = sprintf "H%d" (new_name ())
;;

let new_prop () = sprintf "P%d" (new_name ())
;;

let new_term () = sprintf "X%d" (new_name ())
;;

let declare_header oc =
  fprintf oc "
#NAME test
Term : Type.
Prop: Type.
prf: Prop -> Type.
anyterm: Term.

not: Prop -> Prop.
notc: Prop -> Prop :=
  A:Prop => not (not (not (not (not A)))).
True: Prop.
Truec: Prop := not (not (True)).
False: Prop.
Falsec: Prop := not (not (False)).
and: Prop -> Prop -> Prop.
andc: Prop -> Prop -> Prop :=
  A:Prop => B:Prop => not (not (and (not (not A)) (not (not B)))).
or: Prop -> Prop -> Prop.
orc: Prop -> Prop -> Prop :=
  A:Prop => B:Prop => not (not (or (not (not A)) (not (not B)))).
imply: Prop -> Prop -> Prop.
implyc: Prop -> Prop -> Prop :=
  A:Prop => B:Prop => not (not (imply (not (not A)) (not (not B)))).
forall: (Term -> Prop) -> Prop.
forallc: (Term -> Prop) -> Prop :=
  P:(Term -> Prop) => 
  not (not (forall (x:Term => not (not (P x))))).
exists: (Term -> Prop) -> Prop.
existsc: (Term -> Prop) -> Prop :=
  P:(Term -> Prop) => 
  not (not (exists (x:Term => not (not (P x))))).
equal: Term -> Term -> Prop.
equalc: Term -> Term -> Prop :=
  a:Term => b:Term => not (not (equal a b)).
equiv: Prop -> Prop -> Prop := 
  A:Prop => B:Prop => and (imply A B) (imply B A).


[] prf True --> P:Prop -> (prf P -> prf P)
[] prf False --> P:Prop -> prf P
[A: Prop, B: Prop] prf (and A B) --> P:Prop -> (prf A -> prf B -> prf P) -> prf P
[A: Prop, B: Prop] prf (or A B) --> P:Prop -> (prf A -> prf P) -> (prf B -> prf P) -> prf P
[A: Prop, B: Prop] prf (imply A B) --> prf A -> prf B
[A: Prop] prf (not A) --> prf A -> prf False
[A: Term -> Prop] prf (forall A) --> x:Term -> prf (A x)
[A: Term -> Prop] prf (exists A) --> 
P:Prop -> (x:Term -> prf (A x) -> prf P) -> prf P
[x: Term, y: Term] prf (equal x y) --> P:(Term -> Prop) -> prf (imply (P x) (P y)).\n\n"
;;

let rec p_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args -> 
    fprintf oc "%a %a"
      printer a (p_list printer) args;
;;

let rec p_comma_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args -> 
    fprintf oc "%a, %a" 
      printer a (p_comma_list printer) args;
;;

let rec p_single_arrow_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args -> 
    fprintf oc "%a -> %a" 
      printer a (p_single_arrow_list printer) args;
;;

let rec p_double_arrow_list printer oc l =
  match l with
  | [] -> ()
  | [a] -> fprintf oc "%a" printer a
  | a :: args -> 
    fprintf oc "%a => %a" 
      printer a (p_double_arrow_list printer) args;
;;

let p_var oc e =
match e with
| Evar(s, _) -> fprintf oc "%s" s;
| _ -> assert false
;;

let p_anyterm oc =
  fprintf oc "anyterm"
;;

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
;;

let rec p_expr oc e = 
  match e with
  | Eand (Eimply (e1, e2, _), Eimply (e3, e4, _), _) 
    when (equal e3 e2 && equal e4 e1) ->
    fprintf oc "(equiv %a %a)" p_expr e1 p_expr e2
  | Enot (Enot (Enot (Enot (Enot (e, _), _), _), _), _) ->
    fprintf oc "(notc %a)" p_expr e
  | Enot (Enot ( Eand (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    fprintf oc "(andc %a %a)" p_expr e1 p_expr e2
  | Enot (Enot ( Eor (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    fprintf oc "(orc %a %a)" p_expr e1 p_expr e2
  | Enot (Enot ( Eimply (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    fprintf oc "(implyc %a %a)" p_expr e1 p_expr e2
  | Enot (Enot (Etrue, _), _) -> fprintf oc "Truec"
  | Enot (Enot (Efalse, _), _) -> fprintf oc "Falsec"
  | Enot (Enot (
    Eall (Evar (x, _), s, Enot (Enot (e, _), _), _), _), _) ->
    fprintf oc "(forallc (%s:Term => %a))" x p_expr e
  | Enot (Enot (
    Eex (Evar (x, _), s, Enot (Enot (e, _), _), _), _), _) ->
    fprintf oc "(existsc (%s:Term => %a))" x p_expr e
  | Enot (Enot (Eapp (Evar("=", _), [e1;e2], _), _), _) ->
    fprintf oc "(equalc %a %a)" p_expr e1 p_expr e2
  | Evar (v, _) when Mltoll.is_meta v -> 
    fprintf oc "%t" p_anyterm
  | Evar (v, _) -> 
    fprintf oc "%a" p_chars v
  | Eapp (Evar("$string", _), [v], _) -> 
    fprintf oc "S%a" p_expr v
  | Eapp (Evar("=", _), [e1;e2], _) ->
    fprintf oc "(equal %a %a)" p_expr e1 p_expr e2
  | Eapp (Evar(s, _), [], _) ->
    fprintf oc "%a" p_chars s
  | Eapp (Evar(s, _), args, _) ->
    fprintf oc "(%a %a)" p_chars s (p_list p_expr) args
  | Enot (e, _) ->
    fprintf oc "(not %a)" p_expr e
  | Eand (e1, e2, _) ->
    fprintf oc "(and %a %a)" p_expr e1 p_expr e2
  | Eor (e1, e2, _) ->
    fprintf oc "(or %a %a)" p_expr e1 p_expr e2
  | Eimply (e1, e2, _) ->
    fprintf oc "(imply %a %a)" p_expr e1 p_expr e2
  | Etrue -> fprintf oc "True"
  | Efalse -> fprintf oc "False"
  | Eall (Evar (x, _), s, e, _) ->
    fprintf oc "(forall (%s:Term => %a))" x p_expr e
  | Eex (Evar (x, _), s, e, _) ->
    fprintf oc "(exists (%s:Term => %a))" x p_expr e
  | Elam _ -> fprintf oc "errorlam"
  | Eequiv (e1, e2, _) -> fprintf oc "(equiv %a %a)" p_expr e1 p_expr e2
  | Emeta _ -> fprintf oc "errormeta"
  | Eall _ -> fprintf oc "errorall"
  | Eex _ -> fprintf oc "errorex"
  | Etau _ -> assert false
  | _ -> assert false
;;

let rec p_expr2 oc e = 
  match e with
  | Eand (Eimply (e1, e2, _), Eimply (e3, e4, _), _) 
    when (equal e3 e2 && equal e4 e1) ->
    fprintf oc "equiv %a %a" p_expr e1 p_expr e2
  | Enot (Enot (Enot (Enot (Enot (e, _), _), _), _), _) ->
    fprintf oc "notc %a" p_expr e
  | Enot (Enot ( Eand (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    fprintf oc "andc %a %a" p_expr e1 p_expr e2
  | Enot (Enot ( Eor (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    fprintf oc "orc %a %a" p_expr e1 p_expr e2
  | Enot (Enot ( Eimply (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    fprintf oc "implyc %a %a" p_expr e1 p_expr e2
  | Enot (Enot (Etrue, _), _) -> fprintf oc "Truec"
  | Enot (Enot (Efalse, _), _) -> fprintf oc "Falsec"
  | Enot (Enot (
    Eall (Evar (x, _), s, Enot (Enot (e, _), _), _), _), _) ->
    fprintf oc "forallc (%s:Term => %a)" x p_expr e
  | Enot (Enot (
    Eex (Evar (x, _), s, Enot (Enot (e, _), _), _), _), _) ->
    fprintf oc "existsc (%s:Term => %a)" x p_expr e
  | Enot (Enot (Eapp (Evar("=", _), [e1;e2], _), _), _) ->
    fprintf oc "equalc %a %a" p_expr e1 p_expr e2
  | Evar (v, _) when Mltoll.is_meta v -> 
    fprintf oc "%t" p_anyterm
  | Evar (v, _) -> 
    fprintf oc "%a" p_chars v
  | Eapp (Evar("$string", _), [v], _) -> 
    fprintf oc "S%a" p_expr v
  | Eapp (Evar("=", _), [e1;e2], _) ->
    fprintf oc "equal %a %a" p_expr e1 p_expr e2
  | Eapp (Evar(s, _), [], _) ->
    fprintf oc "%a" p_chars s
  | Eapp (Evar(s, _), args, _) ->
    fprintf oc "%a %a" p_chars s (p_list p_expr) args
  | Enot (e, _) ->
    fprintf oc "not %a" p_expr e
  | Eand (e1, e2, _) ->
    fprintf oc "and %a %a" p_expr e1 p_expr e2
  | Eor (e1, e2, _) ->
    fprintf oc "or %a %a" p_expr e1 p_expr e2
  | Eimply (e1, e2, _) ->
    fprintf oc "imply %a %a" p_expr e1 p_expr e2
  | Etrue -> fprintf oc "True"
  | Efalse -> fprintf oc "False"
  | Eall (Evar (x, _), s, e, _) ->
    fprintf oc "forall (%s:Term => %a)" x p_expr e
  | Eex (Evar (x, _), s, e, _) ->
    fprintf oc "exists (%s:Term => %a)" x p_expr e
  | Elam _ -> fprintf oc "errorlam"
  | Eequiv (e1, e2, _) -> fprintf oc "equiv %a %a" p_expr e1 p_expr e2
  | Emeta _ -> fprintf oc "errormeta"
  | Eall _ -> fprintf oc "errorall"
  | Eex _ -> fprintf oc "errorex"
  | Etau _ -> assert false
  | _ -> assert false
;;

let p_prf oc e = 
  fprintf oc "prf %a" p_expr e
;;

let p_declare oc (e, printer) =
  fprintf oc "%t : %a" printer p_expr e;
;; 

let p_declare_prf oc (e, printer) =
  fprintf oc "%t : %a" printer p_prf e;
;;

let p_str s oc = 
  fprintf oc "%s" s;
;;

(* the left part of sequents can only grow: the left part of the conclusion is always contained in the left part of the hypothesis
weakening is implicit*)
let rec p_proof oc (lkproof, goal, gamma) =
  let poc fmt = fprintf oc fmt in
  let g, d, lkrule = lkproof in
  let p_hyp oc e =
    let f = Lltolj.use_defs e in
    try (List.assoc f gamma) oc
    with Not_found -> (print_endline "    --    "; 
		       p_expr oc e;
		       print_endline "    --    ";
		       fprintf oc "axiom error") in
  match lkrule with
  | SCaxiom (e) -> 
    poc "%a" p_hyp e
  | SCfalse -> 
    poc "(%a %a)" p_hyp efalse p_expr goal
  | SCtrue -> 
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(%s : Prop => %s : prf %s => %s)"
      prop var prop var
  | SCeqref (a) -> 
    let prop = new_prop () in
    poc "(%s : (Term -> Prop) => %a)"
      prop p_proof (
	scrimply (
	  eapp (evar(prop), [a]), 
	  eapp (evar(prop), [a]), 
	  scaxiom (eapp (evar(prop), [a]), [])),
	eimply (eapp (evar(prop), [a]), eapp (evar(prop), [a])), gamma)
      (*p_proof (
	scrand (
	  eimply (eapp (prop, [a]), eapp (prop, [a])),
	  eimply (eapp (prop, [a]), eapp (prop, [a])),
	  scrimply (
	    eapp (prop, [a]), 
	    eapp (prop, [a]), 
	    scaxiom (eapp (prop, [a]), [])),
	  scrimply (
	    eapp (prop, [a]), 
	    eapp (prop, [a]), 
	    scaxiom (eapp (prop, [a]), []))),
	eand (
	  eimply (eapp (prop, [a]), eapp (prop, [a])),
	  eimply (eapp (prop, [a]), eapp (prop, [a]))), gamma)*)
  | SCeqsym (a, b) -> 
(*    let prop = new_prop () in
    let imp1 = eimply (eapp (prop, [a]), eapp (prop, [b])) in
    let imp2 = eimply (eapp (prop, [b]), eapp (prop, [a])) in
    let eq = eand (imp1, imp2) in
    let var1 = new_hypo () in
    let var2 = new_hypo () in*)
    let term = new_term () in
    poc "(%a (%s:Term => %a) %a)"
      p_hyp (eapp (evar("="), [a; b]))
      term p_expr (eapp (evar("="), [evar term; a]))
      p_proof (sceqref (a, []), eapp (evar("="), [a; a]), gamma)
  (*p_proof (
	scland (imp1, imp2, scrand (
	  imp2, imp1,
	  scaxiom ( eimply (
	    eapp (prop, [b]), eapp (prop, [a])), [imp1]),
	  scaxiom ( eimply ( 
	    eapp (prop, [a]), eapp (prop, [b])), [imp2]))),
	eand (imp2, imp1), 
	(imp1, fun oc ->
	  fprintf oc "(%a %s %a (%a => %a => %s))"
	    p_hyp (eapp ("=", [a; b])) prop p_expr imp1
	    p_declare_prf (imp1, p_str var1)
	    p_declare_prf (imp2, p_str var2) var1) ::
	  (imp2, fun oc ->
	    fprintf oc "(%a %s %a (%a => %a => %s))"
	      p_hyp (eapp ("=", [a; b])) prop p_expr imp2
	      p_declare_prf (imp1, p_str var1)
	      p_declare_prf (imp2, p_str var2) var2) ::
	  (eq, fun oc -> 
	    fprintf oc "(%a %s)"
	      p_hyp (eapp ("=",[a; b])) prop) ::
	  gamma)*)
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
      (lkrule, goal, (Lltolj.use_defs (substitute [(x, t)] p), p_aux) :: gamma)
  | SClex (Eex (x, ty, p, _) as ep, v, lkrule) ->
    let q = Lltolj.use_defs (substitute [(x, v)] p) in    
    let var = new_hypo () in
    poc "(%a %a (%a:Term => %s:prf %a => %a))"
      p_hyp ep p_expr goal
      p_expr v var p_expr q 
      p_proof
      (lkrule, goal, (q, p_str var) :: gamma)
  | SCrand (e1, e2, lkrule1, lkrule2) ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(%s : Prop => %s : (%a -> %a -> prf %s) => %s %a %a)"
      prop var
      p_prf e1 p_prf e2 prop
      var p_proof (lkrule1, e1, gamma) p_proof (lkrule2, e2, gamma)
  | SCrorl (e1, e2, lkrule) ->
    let prop = new_prop () in
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%s : Prop => %s : (%a -> prf %s) => %s : (%a -> prf %s) => %s %a)"
      prop var1 p_prf e1 prop var2 p_prf e2 prop
      var1 p_proof (lkrule, e1, gamma)
  | SCrorr (e1, e2, lkrule) ->
    let prop = new_prop () in
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%s : Prop => %s : (%a -> prf %s) => %s : (%a -> prf %s) => %s %a)"
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
    let q = Lltolj.use_defs (substitute [(x, v)] p) in
    poc "(%a:Term => %a)"
      p_expr v p_proof
      (lkrule, q, gamma)
  | SCrex (Eex (x, ty, p, _), t, lkrule) ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(%s:Prop => %s: (%a:Term -> prf %a -> prf %s) => %s %a %a)"
      prop var 
      p_expr x p_expr p prop
      var p_expr t 
      p_proof (lkrule, Lltolj.use_defs (substitute [(x, t)] p), gamma)
  | SCcnot (e, lkrule) -> 
    poc "proof must be constructive"
  | SClcontr (e, lkrule) ->
    poc "%a"
      p_proof (lkrule, goal, gamma)
  | SCrweak (e, lkrule) -> 
    poc "(%a %a)"
      p_proof (lkrule, efalse, gamma)
      p_expr e
  | SCeqfunc (Eapp (Evar(p, _), ts, _), Eapp (_, us, _)) -> 
    let pred = new_prop () in
    let var = new_hypo () in
    let rec itereq oc (xts, ts, us) =
      match ts, us with
      | [], [] -> fprintf oc "%s" var
      | t :: ts, u :: us ->
	(*let var1 = new_hypo () in
	  let var2 = new_hypo () in*)
	let term = new_term () in
	poc "(%a (%s:Term => %a) %a)" 
	  p_hyp (eapp (evar("="), [t; u]))
	  term p_expr 
	  (eapp (evar(pred), [eapp (evar(p), xts @ ((evar term) :: us))]))
	  itereq ((xts@[t]), ts, us)
      | _ -> assert false;
    in
    poc "(%s:(Term -> Prop) => %s:prf %a => %a)"
      pred var p_expr (eapp (evar(pred), [eapp (evar(p), ts)]))
      itereq ([], ts, us)      
  | SCeqprop (Eapp (Evar(p, _), ts, _), Eapp (_, us, _)) -> 
    let rec itereq oc (xts, ts, us) =
      match ts, us with
      | [], [] -> fprintf oc "%a" p_hyp (eapp (evar(p), xts))
      | t :: ts, u :: us ->
	(*let var1 = new_hypo () in
	let var2 = new_hypo () in*)
	let term = new_term () in
	poc "(%a (%s:Term => %a) %a)" 
	  p_hyp (eapp (evar("="), [t; u]))
	  term p_expr (eapp (evar(p), xts @ ((evar term) :: us)))
	  itereq ((xts@[t]), ts, us)
      | _ -> assert false;
    in 
    poc "%a" itereq ([], ts, us)
  (*    let rec itereq oc (xts, ts, us) =
      match ts, us with
      | [], [] -> fprintf oc "%a" p_hyp (eapp (p, xts))
      | t :: ts, u :: us ->
	let var1 = new_hypo () in
	let var2 = new_hypo () in
	let term = new_term () in
	poc "(%a (%s:Term => %a) %a (%a => %a => %s %a))" 
	  p_hyp (eapp ("=", [t; u]))
	  term p_expr (eapp (p, xts @ ((evar term) :: us)))
	  p_expr (eapp (p, xts @ (u :: us)))
	  p_declare_prf (
	    eimply (
	      eapp (p, xts @ (t :: us)), 
	      eapp (p, xts @ (u :: us))), 
	    p_str var1)
	  p_declare_prf (
	    eimply (
	      eapp (p, xts @ (u :: us)), 
	      eapp (p, xts @ (t :: us))), 
	    p_str var2)
	  var1 itereq ((xts@[t]), ts, us)
      | _ -> assert false;
    in 
    poc "%a" itereq ([], ts, us)*)
  | _ -> assert false;
;;

let rec p_tree oc proof goal =
  let ljproof = lltolj proof goal in
  let _, conc, _ = ljproof in
  fprintf oc "conjecture_proof : %a :=\n"
    p_prf conc;
  fprintf oc "%a."
    p_proof (ljproof, conc, []) 
;;

let rec get_goal phrases =
  match phrases with
  | [] -> None
  | Phrase.Hyp (name, e, _) :: _ when name = goal_name -> Some e
  | _ :: t -> get_goal t
;;

let p_theorem oc phrases l =
  match l with
  | [] -> assert false
  | thm :: lemmas ->
    List.iter 
      (fun lemma -> 
	Hashtbl.add Lltolj.lemma_env lemma.name lemma.proof)
      lemmas;
    let goal = get_goal phrases in
    p_tree oc thm.proof goal;
;;

type result =
  | Prop
  | Term
  | Indirect of string
;;
type signature =
  | Default of int * result
;;

let predefined = ["="; "$string"]
;;

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
    | Eapp (Evar("$string", _), [Evar (s, _)], _) ->
      (if not (List.mem_assoc e !Lltolj.distinct_terms)
       then 
	  Lltolj.distinct_terms := 
	    (e, (List.length !Lltolj.distinct_terms) + 1) 
	  :: !Lltolj.distinct_terms; add_sig ("S"^s) 0 Term)
    | Eapp (Evar(s, _), args, _) ->
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
    | _ -> assert false
  in
  let do_phrase p = 
    match p with
      | Phrase.Hyp (name, e, _) ->
	get_sig Prop [] e;
      | Phrase.Def (DefReal ("", s, _, e, None)) ->
	get_sig (Indirect s) [] e;
      | Phrase.Rew (name, e, _) -> 
        get_sig Prop [] e;
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
;;

let p_signature oc (sym, sign) =
  let rec p_arity n =
    if n = 0 then () else begin
      fprintf oc "Term -> ";
      p_arity (n-1);
    end;
  in
  fprintf oc "%a : " p_expr (evar sym);
  match sign with
  | Default (arity, kind) ->
      begin
        p_arity arity;
        match kind with
        | Prop -> fprintf oc "Prop.\n";
        | Term -> fprintf oc "Term.\n";
        | _ -> assert false;
      end;
;;

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
  | Phrase.Rew (name, stmt, _) -> ()
  | _ -> assert false
;;

let rec add_distinct_terms_axioms l =
  match l with
  | (x, n) :: (y, m) :: l -> 
    Lltolj.hypothesis_env := 
      enot (eapp (evar("="), [y; x])) :: !Lltolj.hypothesis_env;
    add_distinct_terms_axioms ((x, n) :: l);
    add_distinct_terms_axioms ((y, m) :: l);
  | _ -> ()
;;

let timeout = ref 10;;

let get_rew_context sigs expr = 
  let terms =
    List.map (fun (sym, _) -> sym) sigs in
  let l = ref [] in
  let rec get_sig env e =
    match e with
    | Evar (s, _) -> if not (List.mem s env || List.mem e !l) then l := e :: !l;
    | Emeta  _ | Etrue | Efalse -> ()
    | Eapp (Evar(s, _), args, _) ->
      List.iter (get_sig env) args;
    | Eand (e1, e2, _) | Eor (e1, e2, _)
    | Eimply (e1, e2, _) | Eequiv (e1, e2, _) 
      -> get_sig env e1;
	 get_sig env e2;
    | Enot (e1, _) -> get_sig env e1;
    | Eall (Evar (v, _), _, e1, _) | Eex (Evar (v, _), _, e1, _)
      -> get_sig (v::env) e1;
    | Eex _ | Eall _ | Etau _ | Elam _ -> assert false
    | _ -> assert false
  in
  get_sig terms expr;
  !l
;;
(*
let get_rews sym (left, right) assoc_rew = 
  if List.mem_assoc sym assoc_rew
  then 
    let l = List.assoc sym assoc_rew in
    (sym, ((left, right) :: l)) :: 
      (List.remove_assoc sym assoc_rew);
  else
    (sym, [(left, right)]) :: assoc_rew;
;;*)

let get_rews sym (left, right) assoc_rew = 
  if List.mem_assoc sym assoc_rew
  then 
    let list = List.assoc sym assoc_rew in
    (sym, (left, right) :: list) :: List.remove_assoc sym assoc_rew
   (* let l_f = List.sort Pervasives.compare l in
    l_f*)
  else
    (sym, [(left, right)]) :: assoc_rew;
;;


let rec p_rews oc sigs (sym, list) =
  match list with
  | [] -> assert false
  | [(left, right)] ->
    let l = get_rew_context sigs left in
    fprintf oc "[%a] " (
      p_comma_list 
	(fun oc e -> fprintf oc "%a : Term" p_var e)) l;
    fprintf oc "%a " p_expr2 left;
    fprintf oc "--> %a.\n" p_expr right;
  | (left, right) :: list -> 
    let l = get_rew_context sigs left in
    fprintf oc "[%a] " (
      p_comma_list 
	(fun oc e -> fprintf oc "%a : Term" p_var e)) l;
    fprintf oc "%a " p_expr2 left;
    fprintf oc "--> %a\n" p_expr right;
    p_rews oc sigs (sym, list);
;;

let output oc phrases ppphrases llp =
  (*eprintf "%a" 
    (fun oc x -> Print.llproof (Print.Chan oc) x)
    llp;*)
  Lltolj.hypothesis_env := [];
  declare_header oc;
  let sigs = get_signatures phrases in
  List.iter (p_signature oc) sigs;
  List.iter (declare_hyp oc) phrases;
  let assoc_rew =
    Hashtbl.fold get_rews !Expr.tbl_term [] in
  let assoc_rew2 = 
    Hashtbl.fold get_rews !Expr.tbl_prop assoc_rew in
  
  List.iter (p_rews oc sigs) assoc_rew2 ;
  add_distinct_terms_axioms !Lltolj.distinct_terms;
  p_theorem oc phrases (List.rev llp);
;;
