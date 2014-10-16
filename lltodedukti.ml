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

(* the left part of sequents can only grow: the left part of the conclusion is always contained in the left part of the hypothesis
weakening is implicit*)

let rec trproof (lkproof, goal, gamma) =
  let g, d, lkrule = lkproof in
  let trhyp e =
    try (List.assoc e gamma)
    with Not_found -> assert false in
  match lkrule with
  | SCaxiom (e) ->
    trhyp e
  | SCfalse ->
    Dk.dkapp2 (trhyp efalse) (trexpr goal)
  | SCtrue ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkprop Dk.dkproptype (Dk.dklam dkvar (Dk.dkprf dkprop) dkvar)
  | SCeqref (a) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    Dk.dklam dkprop (Dk.dkarrow Dk.dktermtype Dk.dkproptype)
      (trproof (
	scrimply (
	  eapp (prop, [a]),
	  eapp (prop, [a]),
	  scaxiom (eapp (prop, [a]), [])),
	eimply (eapp (prop, [a]), eapp (prop, [a])), gamma))
  | SCeqsym (a, b) ->
    let term = new_term () in
    let dkterm = Dk.dkvar term in
    Dk.dkapp3 (trhyp (eapp ("=", [a; b]))) 
      (Dk.dklam dkterm Dk.dktermtype (trexpr (eapp ("=", [evar term; a])))) 
      (trproof (sceqref (a, []), eapp ("=", [a; a]), gamma))
  | SCcut (e, lkrule1, lkrule2) ->
    trproof
      (lkrule2, goal,
       (e, trproof (lkrule1, e, gamma)) :: gamma)
  | SCland (e1, e2, lkrule) ->
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
    Dk.dkapp3 (trhyp (eand (e1, e2))) 
      (trexpr goal)
      (Dk.dklam dkvar1 
	 (Dk.dkprf (trexpr e1)) 
	 (Dk.dklam dkvar2 
	    (Dk.dkprf (trexpr e2)) 
	    (trproof (lkrule, goal, (e1, dkvar1) :: (e2, dkvar2) :: gamma))))
  | SClor (e1, e2, lkrule1, lkrule2) ->
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
      Dk.dkapp (trhyp (eor (e1, e2)))
      [trexpr goal;
       Dk.dklam dkvar1 
	 (Dk.dkprf (trexpr e1))
	 (trproof (lkrule1, goal, (e1, (Dk.dkvar var1)) :: gamma));
       Dk.dklam dkvar2
	 (Dk.dkprf (trexpr e2))
	 (trproof (lkrule2, goal, (e2, (Dk.dkvar var2)) :: gamma))]
  | SClimply (e1, e2, lkrule1, lkrule2) ->
    let traux =
      Dk.dkapp2 (trhyp (eimply (e1, e2))) (trproof (lkrule1, e1, gamma)) in
      trproof (lkrule2, goal, (e2, traux) :: gamma)
  | SClnot (e, lkrule) ->
    Dk.dkapp2 (trhyp (enot e)) (trproof (lkrule, e, gamma))
  | SClall (Eall (x, ty, p, _) as ap, t, lkrule) ->
    let traux =
      Dk.dkapp2 (trhyp ap) (trexpr t) in
      trproof
      (lkrule, goal, (substitute [(x, t)] p, traux) :: gamma)
  | SClex (Eex (x, ty, p, _) as ep, v, lkrule) ->
    let q = substitute [(x, v)] p in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dkapp3 (trhyp ep)
      (trexpr goal)
      (Dk.dklam (trexpr v) Dk.dktermtype
	 (Dk.dklam dkvar 
	    (Dk.dkprf (trexpr q))
	    (trproof  (lkrule, goal, (q,dkvar) :: gamma))))
  | SCrand (e1, e2, lkrule1, lkrule2) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkprop Dk.dkproptype
       (Dk.dklam dkvar 
	  (Dk.dkarrow (Dk.dkprf (trexpr e1)) 
	     (Dk.dkarrow (Dk.dkprf (trexpr e2)) (Dk.dkprf dkprop)))
	  (Dk.dkapp3 dkvar (trproof (lkrule1, e1, gamma)) (trproof (lkrule2, e2, gamma))))     
  | SCrorl (e1, e2, lkrule) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
    Dk.dklam dkprop Dk.dkproptype
      (Dk.dklam dkvar1 
	 (Dk.dkarrow (Dk.dkprf (trexpr e1)) (Dk.dkprf dkprop))
	 (Dk.dklam dkvar2 
	    (Dk.dkarrow (Dk.dkprf (trexpr e2)) (Dk.dkprf dkprop)) 
	    (Dk.dkapp2 dkvar1 (trproof (lkrule, e1, gamma)))))
  | SCrorr (e1, e2, lkrule) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
    Dk.dklam dkprop Dk.dkproptype
      (Dk.dklam dkvar1 
	 (Dk.dkarrow (Dk.dkprf (trexpr e1)) (Dk.dkprf dkprop))
	 (Dk.dklam dkvar2 
	    (Dk.dkarrow (Dk.dkprf (trexpr e2)) (Dk.dkprf dkprop)) 
	    (Dk.dkapp2 dkvar2 (trproof (lkrule, e2, gamma)))))
  | SCrimply (e1, e2, lkrule) ->
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkvar (Dk.dkprf (trexpr e1))
      (trproof (lkrule, e2, (e1, dkvar) :: gamma))
  | SCrnot (e, lkrule) ->
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkvar (Dk.dkprf (trexpr e))
      (trproof (lkrule, efalse, (e, dkvar) :: gamma))
  | SCrall (Eall (x, ty, p, _), v, lkrule) ->
    let q = substitute [(x, v)] p in
    Dk.dklam (trexpr v) Dk.dktermtype 
      (trproof (lkrule, q, gamma))
  | SCrex (Eex (x, ty, p, _), t, lkrule) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkprop Dk.dkproptype
      (Dk.dklam dkvar 
	 (Dk.dkpi (trexpr x) (Dk.dktermtype) 
	    (Dk.dkarrow (Dk.dkprf (trexpr p)) (Dk.dkprf dkprop))) 
	 (Dk.dkapp3 dkvar (trexpr t) (trproof (lkrule, substitute [(x, t)] p, gamma))))
  | SCcnot (e, lkrule) -> assert false
  | SClcontr (e, lkrule) ->
      trproof (lkrule, goal, gamma)
  | SCrweak (e, lkrule) ->
    Dk.dkapp2 (trproof (lkrule, efalse, gamma)) (trexpr e)
  | SCeqfunc (Eapp (p, ts, _), Eapp (_, us, _)) ->
    let pred = new_prop () in
    let dkpred = Dk.dkvar pred in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    let rec itereq (xts, ts, us) =
      match ts, us with
      | [], [] -> Dk.dkvar var
      | t :: ts, u :: us ->
	let term = new_term () in
	let dkterm = Dk.dkvar term in
	Dk.dkapp3 (trhyp (eapp ("=", [t; u]))) 
	  (Dk.dklam dkterm Dk.dktermtype 
	     (trexpr (eapp (pred, [eapp (p, xts @ ((evar term) :: us))])))) 
	  (itereq ((xts@[t]), ts, us))
      | _ -> assert false in
    Dk.dklam dkpred (Dk.dkarrow Dk.dktermtype Dk.dkproptype) 
      (Dk.dklam dkvar (Dk.dkprf (trexpr (eapp (pred, [eapp (p, ts)])))) 
	 (itereq ([], ts, us)))
  | SCeqprop (Eapp (p, ts, _), Eapp (_, us, _)) ->
    let rec itereq (xts, ts, us) =
      match ts, us with
      | [], [] -> trhyp (eapp (p, xts))
      | t :: ts, u :: us ->
	let term = new_term () in
	let dkterm = Dk.dkvar term in
	Dk.dkapp3 (trhyp (eapp ("=", [t; u]))) 
	  (Dk.dklam dkterm Dk.dktermtype ((trexpr (eapp (p, xts @ ((evar term) :: us)))))) 
	  (itereq ((xts@[t]), ts, us))
      | _ -> assert false;
    in
    itereq ([], ts, us)
  | _ -> assert false

let rec p_tree oc proof goal =
  let ljproof = lltolj proof goal in
  let conc = scconc ljproof in
  fprintf oc "conjecture_proof : %a :=\n"
    Dk.p_term_p (Dk.dkprf (trexpr conc));
  fprintf oc "%a."
    Dk.p_term (trproof (ljproof, conc, []))
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
  fprintf oc "%a : " Dk.p_term_p (trexpr (evar sym));
  match sign with
  | Default (arity, kind) ->
    p_arity arity;
    match kind with
    | Prop -> fprintf oc "logic.Prop.\n";
    | Term -> fprintf oc "logic.Term.\n";
    | _ -> assert false

let find_signature sign =
    match sign with
    | Default (arity, kind) ->
      let endtype =
	match kind with
	| Prop -> Dk.dkproptype
	| Term -> Dk.dktermtype
	| _ -> assert false in
      let rec add_arrow n =
	if n = 0 then endtype else
	  Dk.dkarrow Dk.dktermtype (add_arrow (n-1)) in
      add_arrow arity

let declare_hyp h =
  match h with
  | Phrase.Hyp (name, _, _) when name = goal_name -> ()
  | Phrase.Hyp (name, stmt, _) ->
    Lltolj.hypothesis_env :=
      stmt :: !Lltolj.hypothesis_env
  | Phrase.Def (DefReal (_, sym, params, body, None)) ->
    Hashtbl.add Lltolj.definition_env
      sym (params, body)
  | Phrase.Def (DefReal (_, sym, params, body, Some _)) -> assert false
  | Phrase.Def (DefPseudo (_, _, _, _)) -> assert false
  | Phrase.Def (DefRec (_, _, _, _)) -> assert false
  | Phrase.Sig _ -> assert false
  | Phrase.Inductive _ -> assert false      (* TODO: to implement *)

let p_hyp oc sigs h =
  match h with
  | Phrase.Hyp (name, _, _) when name = goal_name -> ()
  | Phrase.Hyp (name, stmt, _) -> ()
  | Phrase.Def (DefReal ("", sym, params, body, None)) ->
    let vars, types =
      List.split
	(List.map
	   (fun e -> match e with
	   | Evar (v, _) -> let t = find_signature (List.assoc v sigs) in trexpr e, t
	   | _ -> assert false) params) in
    Dk.p_line oc
      (Dk.dkrewrite (List.combine vars types)
	 (Dk.dkapp (Dk.dkvar sym) vars) (trexpr body))
  | _ -> assert false

let rec add_distinct_terms_axioms l =
  match l with
  | (x, n) :: (y, m) :: l ->
    Lltolj.hypothesis_env :=
      enot (eapp ("=", [y; x])) :: !Lltolj.hypothesis_env;
    add_distinct_terms_axioms ((x, n) :: l);
    add_distinct_terms_axioms ((y, m) :: l);
  | _ -> ()

let modname name =
  let buf = Buffer.create (2*String.length name) in
  String.iter
    (fun c -> match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' -> Buffer.add_char buf c
    | '_' -> Buffer.add_string buf "__"
    | _ -> Buffer.add_string buf ("_"^(string_of_int (int_of_char c)))) name;
  Buffer.add_string buf "todk";
  Buffer.contents buf

let output oc phrases ppphrases llp filename =
  Lltolj.hypothesis_env := [];
  Dk.p_line oc (Dk.dkprelude (modname filename));
  let sigs = get_signatures phrases in
  List.iter (p_signature oc) sigs;
  List.iter declare_hyp phrases;
  List.iter (p_hyp oc sigs) phrases;
  add_distinct_terms_axioms !Lltolj.distinct_terms;
  p_theorem oc phrases (List.rev llp)

let outputterm oc phrases ppphrases llp =
  Lltolj.hypothesis_env := [];
  add_distinct_terms_axioms !Lltolj.distinct_terms;
  List.iter declare_hyp phrases;
  p_theorem oc phrases (List.rev llp)
