open Printf;;
open Expr;;
open Llproof;;
open Namespace;;
open Lltolj;;

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
  fprintf oc "Term : Type.
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
tau: (Term -> Prop) -> Term.
maketau :
P: (Term -> Prop) -> t:Term -> prf (P t) -> prf (P (tau P)).
usetau :
P: (Term -> Prop) -> t:Term -> 
prf (P (tau (x: Term => not (P x)))) -> prf (P t).

[] prf True --> P:Prop -> (prf P -> prf P)
[] prf False --> P:Prop -> prf P
[A: Prop, B: Prop] prf (and A B) --> P:Prop -> (prf A -> prf B -> prf P) -> prf P
[A: Prop, B: Prop] prf (or A B) --> P:Prop -> (prf A -> prf P) -> (prf B -> prf P) -> prf P
[A: Prop, B: Prop] prf (imply A B) --> prf A -> prf B
[A: Prop] prf (not A) --> prf A -> prf False
[A: Term -> Prop] prf (forall A) --> 
prf (A (tau (x:Term => not (A x))))
[A: Term -> Prop] prf (exists A) --> prf (A (tau A))
[x: Term, y: Term] prf (equal x y) --> P:(Term -> Prop) -> prf (and (imply (P x) (P y)) (imply (P y) (P x))).\n\n"
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

let rec p_expr oc e = 
  match e with
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
  | Enot (Enot (Eapp ("=", [e1;e2], _), _), _) ->
    fprintf oc "(equalc %a %a)" p_expr e1 p_expr e2
  | Evar (v, _) when Mltoll.is_meta v -> 
    fprintf oc "%t" p_anyterm
  | Evar (v, _) -> fprintf oc "%s" v
  | Eapp ("=", [e1;e2], _) ->
    fprintf oc "(equal %a %a)" p_expr e1 p_expr e2
  | Eapp (s, [], _) ->
    fprintf oc "%s" s
  | Eapp (s, args, _) ->
    fprintf oc "(%s %a)" s (p_list p_expr) args
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
  | Etau (Evar (x, _), s, e, _) ->
    fprintf oc "(tau (%s:Term => %a))" x p_expr e
  | Elam _ -> fprintf oc "errorlam"
  | Eequiv _ -> fprintf oc "errorequiv"
  | Emeta _ -> fprintf oc "errormeta"
  | Eall _ -> fprintf oc "errorall"
  | Eex _ -> fprintf oc "errorex"
  | Etau _ -> fprintf oc "errortau"
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
  let p_hyp oc e =
    try (List.assoc e gamma) oc
    with Not_found -> fprintf oc "axiom error" in
  match lkproof with
  | SCAxiom (e) -> 
    poc "%a" p_hyp e
  | SCFalse -> 
    poc "(%a %a)" p_hyp efalse p_expr goal
  | SCTrue -> 
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(%s : Prop => %s : prf %s => %s)"
      prop var prop var
  | SCEqref (a) -> 
    let prop = new_prop () in
    poc "(%s : (Term -> Prop) => %a)"
      prop p_proof (
	SCRand (
	  eimply (eapp (prop, [a]), eapp (prop, [a])),
	  eimply (eapp (prop, [a]), eapp (prop, [a])),
	  SCRimply (
	    eapp (prop, [a]), 
	    eapp (prop, [a]), 
	    SCAxiom (eapp (prop, [a]))),
	  SCRimply (
	    eapp (prop, [a]), 
	    eapp (prop, [a]), 
	    SCAxiom (eapp (prop, [a])))),
	eand (
	  eimply (eapp (prop, [a]), eapp (prop, [a])),
	  eimply (eapp (prop, [a]), eapp (prop, [a]))), gamma)
  | SCEqsym (a, b) -> 
    let prop = new_prop () in
    poc "(%s : (Term -> Prop) => %a)"
      prop p_proof (
	SCLand (
	  eimply (eapp (prop, [a]), eapp (prop, [b])),
	  eimply (eapp (prop, [b]), eapp (prop, [a])),
	  SCRand (
	    eimply (eapp (prop, [b]), eapp (prop, [a])),
	    eimply (eapp (prop, [a]), eapp (prop, [b])),
	    SCAxiom (eimply (eapp (prop, [b]), eapp (prop, [a]))),
	    SCAxiom (eimply (eapp (prop, [a]), eapp (prop, [b]))))),
	eand (
	  eimply (eapp (prop, [b]), eapp (prop, [a])),
	  eimply (eapp (prop, [a]), eapp (prop, [b]))), 
	(eand (eimply (eapp (prop, [a]), eapp (prop, [b])),
	       eimply (eapp (prop, [b]), eapp (prop, [a]))),
	 fun oc -> 
	   fprintf oc "%a %s" p_hyp (eapp ("=", [a; b]))
	     prop) :: gamma)
  | SCCut (e, lkrule1, lkrule2) ->
    poc "%a" p_proof 
      (lkrule2, goal,
       (e, fun oc -> p_proof oc (lkrule1, e, gamma)) :: gamma)
  | SCLand (e1, e2, lkrule) ->
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%a %a (%a => %a => %a))"
      p_hyp (eand (e1, e2)) 
      p_expr goal
      p_declare_prf (e1, p_str var1) p_declare_prf (e2, p_str var2)
      p_proof (lkrule, goal, (e1, p_str var1) :: (e2, p_str var2) :: gamma)
  | SCLor (e1, e2, lkrule1, lkrule2) ->
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(%a %a (%a => %a) (%a => %a))"
      p_hyp (eor (e1, e2))
      p_expr goal
      p_declare_prf (e1, p_str var1) 
      p_proof (lkrule1, goal, (e1, p_str var1) :: gamma)
      p_declare_prf (e2, p_str var2) 
      p_proof (lkrule2, goal, (e2, p_str var2) :: gamma)      
  | SCLimply (e1, e2, lkrule1, lkrule2) ->
    let p_aux oc = 
      fprintf oc "(%a %a)"
	p_hyp (eimply (e1, e2))
	p_proof (lkrule1, e1, gamma) in
    poc "%a"
      p_proof (lkrule2, goal, (e2, p_aux) :: gamma)
  | SCLnot (e, lkrule) ->
    poc "(%a %a)" p_hyp (enot e) p_proof (lkrule, e, gamma)
  | SCLall (Eall (x, ty, p, _) as ap, t, lkrule) ->
    let p_aux oc =
      fprintf oc "(usetau (%a: Term => %a) %a %a)"
	p_expr x p_expr p p_expr t p_hyp ap in
    poc "%a" 
      p_proof 
      (lkrule, goal, (substitute [(x, t)] p, p_aux) :: gamma)
  | SCLex (Eex (x, ty, p, _) as ep, v, lkrule) ->
    let p_aux oc =
      fprintf oc "%a" 
	p_hyp ep in
    let q = substitute [(x, v)] p in    
    poc "%a"
      p_proof
      (lkrule, goal, (q, p_aux) :: gamma)
  | SCLcongruence (p, a, b, lkrule) ->
      let term = new_term () in
      let var1 = new_hypo () in
      let var2 = new_hypo () in
      let p_aux oc =
	fprintf oc "(%a (\n%s: Term => %a) (\n%s : %a => \n%s : %a => %s) %a)"
	  p_hyp (eapp ("=", [a; b]))
	  term p_expr (apply p (evar (term)))
	  var1 p_prf (eimply (apply p a, apply p b))
	  var2 p_prf (eimply (apply p b, apply p a)) var1
	  p_hyp (apply p a) in
      poc "%a"
	p_proof (lkrule, goal, (apply p b, p_aux) :: gamma)
  | SCRand (e1, e2, lkrule1, lkrule2) ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "(\n%s : Prop => \n%s : (%a -> %a -> prf %s) => %s %a %a)"
      prop var
      p_prf e1 p_prf e2 prop
      var p_proof (lkrule1, e1, gamma) p_proof (lkrule2, e2, gamma)
  | SCRorl (e1, e2, lkrule) ->
    let prop = new_prop () in
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(\n%s : Prop => \n%s : (%a -> prf %s) => \n%s : (%a -> prf %s) => 
%s %a)"
      prop var1 p_prf e1 prop var2 p_prf e2 prop
      var1 p_proof (lkrule, e1, gamma)
  | SCRorr (e1, e2, lkrule) ->
    let prop = new_prop () in
    let var1 = new_hypo () in
    let var2 = new_hypo () in
    poc "(\n%s : Prop => \n%s : (%a -> prf %s) => \n%s : (%a -> prf %s) => 
%s %a)"
      prop var1 p_prf e1 prop var2 p_prf e2 prop
      var2 p_proof (lkrule, e2, gamma)
  | SCRimply (e1, e2, lkrule) ->
    let var = new_hypo () in
    poc "(\n%s : %a => %a)"
      var p_prf e1 p_proof (lkrule, e2, (e1, p_str var) :: gamma)
  | SCRnot (e, lkrule) ->
    let var = new_hypo () in
    poc "(%a => %a)" p_declare_prf (e, p_str var) 
      p_proof (lkrule, efalse, (e, p_str var) :: gamma)
  | SCRall (Eall (Evar (x, _), ty, p, _) as ap, v, lkrule) ->
    let p_aux oc =
      fprintf oc "%a" 
	p_hyp ap in
    let q = substitute [(evar x, v)] p in    
    poc "%a"
      p_proof
      (lkrule, goal, (q, p_aux) :: gamma)
  | SCRex (Eex (Evar (x, _), ty, p, _), t, lkrule) ->
    poc "maketau (%s: Term => %a) %a %a"
      x p_expr p p_expr t
      p_proof (lkrule, substitute [(evar (x), t)] p, gamma)
  | SCRweak (e, lkrule) ->
    poc "(%a %a)" p_proof (lkrule, efalse, gamma) p_expr goal
  | SCRcontr (e, lkrule) -> 
    poc "proof must be constructive"
  | _ -> 
    poc "error"
;;

let rec p_tree oc proof goal =
  let conc, lkproof = lltolj proof goal in
  fprintf oc "conjecture_proof : %a :=\n"
    p_prf conc;
  fprintf oc "%a."
    p_proof (lkproof, conc, []);
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
    let goal =  match get_goal phrases with
      | Some (Enot (g, _)) -> g;
      | None -> efalse;
      | _ -> assert false in
    p_tree oc thm.proof goal;
;;

type result =
  | Prop
  | Term
  | Indirect of string
;;
type signature =
  | Default of int * result
  | Hyp_name
;;

let predefined = ["="]
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
  let set_type sym typ =
    Hashtbl.remove symtbl sym;
    Hashtbl.add symtbl sym typ;
  in 
  let do_phrase p = 
    match p with
      | Phrase.Hyp (name, e, _) ->
	get_sig Prop [] e;
	set_type name Hyp_name;
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
	| _ -> assert false
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
      | Hyp_name -> l
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
  fprintf oc "%s : " sym;
  match sign with
  | Default (arity, kind) ->
      begin
        p_arity arity;
        match kind with
        | Prop -> fprintf oc "Prop.\n";
        | Term -> fprintf oc "Term.\n";
        | _ -> assert false;
      end;
  | Hyp_name -> assert false
;;

let declare_hyps oc h =
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
;;

let output oc phrases ppphrases llp =
    declare_header oc;
    let sigs = get_signatures phrases in
    List.iter (p_signature oc) sigs;
    List.iter (declare_hyps oc) phrases;
    p_theorem oc phrases (List.rev llp);
;;
