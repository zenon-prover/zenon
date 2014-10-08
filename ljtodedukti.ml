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

let declare_header oc =
  fprintf oc "#NAME logic.
Term : Type.
Prop: Type.
prf: Prop -> Type.

True: Prop.
False: Prop.
and: Prop -> Prop -> Prop.
or: Prop -> Prop -> Prop.
imply: Prop -> Prop -> Prop.
equiv: Prop -> Prop -> Prop.
not: Prop -> Prop.
forall: (Term -> Prop) -> Prop.
exists: (Term -> Prop) -> Prop.
equal: Term -> Term -> Prop.

[] prf True --> P:Prop -> (prf P -> prf P)
[] prf False --> P:Prop -> prf P
[A: Prop, B: Prop] prf (and A B) --> P:Prop -> (prf A -> prf B -> prf P) -> prf P
[A: Prop, B: Prop] prf (or A B) --> P:Prop -> (prf A -> prf P) -> (prf B -> prf P) -> prf P
[A: Prop, B: Prop] prf (imply A B) --> prf A -> prf B
[A: Prop, B: Prop] prf (equiv A B) --> prf (and (imply A B) (imply B A))
[A: Prop] prf (not A) --> prf A -> prf False
[A: Term -> Prop] prf (forall A) --> x:Term -> prf (A x)
[A: Term -> Prop] prf (exists A) --> P:Prop -> (x:Term -> prf (A x) -> prf P) -> prf P
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

let rec p_expr oc e =
  match e with
  | Evar (v, _) -> fprintf oc "%s" v
  | Emeta (e, _) -> assert false
  | Eapp ("=", [e1;e2], _) ->
    fprintf oc "(equal %a %a)" p_expr e1 p_expr e2
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
  | Eequiv (e1, e2, _) ->
    fprintf oc "(equiv %a %a)" p_expr e1 p_expr e2
  | Etrue -> fprintf oc "True"
  | Efalse -> fprintf oc "False"
  | Eall (Evar (x, _), s, e, _) ->
    fprintf oc "(forall (%s:Term => %a))" x p_expr e
  | Eex (Evar (x, _), s, e, _) ->
    fprintf oc "(exists (%s:Term => %a))" x p_expr e
  | Etau (e1, s, e2, _) ->
    fprintf oc "%s" (Index.make_tau_name e)
  | Elam (Evar (x, _), s, e2, _) ->
    fprintf oc "(lambda (%s:Term => %a))" x p_expr e
  | Eall _ | Eex _ | Elam _ -> assert false
;;

let p_prf oc e =
  fprintf oc "prf %a" p_expr e
;;

let p_declare_prf oc (s,e) =
  fprintf oc "%s : %a" s p_prf e;
;;

let rec p_prove_false oc (proof,l) =
  let poc fmt = fprintf oc fmt in
  match proof.rule, proof.hyps, l with
  | Rfalse, [], [hypo] ->
    poc "%s" hypo
  | Rnottrue, [], [hypo] ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "%s (%s: Prop => %s: prf %s => %s)"
      hypo prop var prop var
  | Raxiom (e), [], [hypo1; hypo2] ->
    poc "%s %s" hypo2 hypo1
  | Rcut (e), _, _ -> assert false
  | Rnoteq (e), [], [hypo] ->
    let prop = new_prop () in
    let var = new_hypo () in
    let var2 = new_hypo () in
    poc "%s (%s:(Term -> Prop) => %s:prf (%s %a) => %s)"
      hypo prop var prop p_expr e var
  | Reqsym (e1, e2), [], [hypo1; hypo2] ->
    let var = new_hypo () in
    let hypo4 = new_hypo () in
    let hypo5 = new_hypo () in
    let prop = new_prop () in
    poc "%s (%s:(Term -> Prop) => %s:prf (%s %a) => %s)"
      hypo2 prop var prop p_expr e2 var
  | Rnotnot (e), [proof], [hypo] ->
    poc "%s %a"
      hypo p_proof proof
  | Rconnect (And, e1, e2), [proof], [hypo] ->
    poc "notequal missing"
  | Rconnect (Or, e1, e2), proofs, _ ->
    poc "notequal missing"
  | Rconnect (Imply, e1, e2), proofs, _ ->
    poc "notequal missing"
  | Rconnect (Equiv, e1, e2), proofs, _ ->
    poc "notequal missing"
  | Rnotconnect (And, e1, e2), [proof1; proof2], [hypo] ->
    let prop = new_prop () in
    let var = new_hypo () in
    poc "%s (%s:Prop =>
(%s: prf %a -> prf %a -> prf %s) =>
%s %a %a)"
      hypo prop var p_expr e1 p_expr e2 prop
      var p_proof proof1 p_proof proof2
  | Rnotconnect (Or, e1, e2), proofs, _ ->
    poc "notequal missing"
  | Rnotconnect (Imply, e1, e2), proofs, _ ->
    poc "notequal missing"
  | Rnotconnect (Equiv, e1, e2), proofs, _ ->
    poc "notequal missing"
  | Rex (e1, e2), [proof], _ ->
    poc "notequal missing"
  | Rall (e1, e2), [proof], _ ->
    poc "notequal missing"
  | Rnotex (e1, e2), [proof], _ ->
    poc "notequal missing"
  | Rnotall (e1, e2), [proof], _ ->
    poc "notequal missing"
  | Rpnotp (e1, e2), proofs, _ ->
    poc "notequal missing"
  | Rnotequal (e1, e2), proofs, _ ->
    poc "notequal missing"
  | RcongruenceLR (e1, e2, e3), [proof], _ ->
    poc "congruence missing"
  | RcongruenceRL (e1, e2, e3), [proof], _ ->
    poc "congruence missing"
  | Rdefinition (name, sym, args, e1, recarg, e2, e3), [proof], _ ->
    poc "definition missing"
  | Rextension (ext, name, args, concs, hyps), proofs, _ ->
    poc "extension missing"
  | Rlemma (name, args), [], _ ->
    poc "lemma missing"
  | _, _, _ -> assert false

and p_proof oc proof =
  let rule_concls = concls_of_rule proof.rule in
  let l = List.fold_left
    (fun l e -> (new_hypo (),e) :: l) [] (List.rev rule_concls) in
  fprintf oc "(%a => %a)"
    (p_double_arrow_list p_declare_prf) l
    p_prove_false (proof,List.map fst l);
;;

let rec p_tree oc proof =
  fprintf oc "conjecture_proof : %a -> prf False :=\n"
    (p_single_arrow_list p_prf) proof.conc;
  fprintf oc "%a." p_proof (translate proof);
;;

let rec p_theorem oc l =
  match l with
  | [] -> assert false
  | thm :: lemmas ->
    p_tree oc thm.proof;
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

let is_nat s =
  try
    for i = 0 to String.length s - 1 do
      if not (Misc.isdigit s.[i]) then raise Exit;
    done;
    true
  with Exit -> false
;;

let predefined = ["="]
;;

let rec get_signatures ps =
  let symtbl = (Hashtbl.create 97 : (string, signature) Hashtbl.t) in
  let defined = ref (predefined) in
  let add_sig sym arity kind =
    if not (Hashtbl.mem symtbl sym) then
      Hashtbl.add symtbl sym (Default (arity, kind))
  in
  let rec get_sig r env e =
    match e with
    | Evar (s, _) when is_nat s -> ()
    | Evar (s, _) -> if not (List.mem s env) then add_sig s 0 r;
    | Emeta  _ | Etrue | Efalse -> ()
    | Eapp (s, args, _) ->
        add_sig s (List.length args) r;
	List.iter (get_sig Term env) args;
    | Eand (e1, e2, _) | Eor (e1, e2, _)
    | Eimply (e1, e2, _) | Eequiv (e1, e2, _)
      -> get_sig Prop env e1;
	 get_sig Prop env e1;
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
	defined := s :: !defined;
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
    if List.mem sym !defined then l
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
    fprintf oc "%s : prf %a.\n" name p_expr stmt;
  | Phrase.Def (DefReal ("", sym, params, body, None)) ->
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
  p_theorem oc (List.rev llp);
;;
