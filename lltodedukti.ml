open Printf
open Expr
open Llproof
open Namespace

module Translate (Out : Ljtodk.TermSig) =
struct

  module LjToDk = Ljtodk.Translate(Out)

  let rec trexpr e =
    match e with
    | Eand (Eimply (e1, e2, _), Eimply (e3, e4, _), _)
        when (equal e3 e2 && equal e4 e1) -> Out.mk_equiv (trexpr e1) (trexpr e2)
    | Enot (Enot (Enot (Enot (Enot (e, _), _), _), _), _) ->
       Out.mk_notc (trexpr e)
    | Enot (Enot ( Eand (
      Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
       Out.mk_andc (trexpr e1) (trexpr e2)
    | Enot (Enot ( Eor (
      Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
       Out.mk_orc (trexpr e1) (trexpr e2)
    | Enot (Enot ( Eimply (
      Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
       Out.mk_implyc (trexpr e1) (trexpr e2)
    | Enot (Enot (Etrue, _), _) -> Out.mk_truec
    | Enot (Enot (Efalse, _), _) -> Out.mk_falsec
    | Enot (Enot (
      Eall (e1, s, Enot (Enot (e2, _), _), _), _), _) ->
       Out.mk_forallc (trexpr e1) (trexpr e2)
    | Enot (Enot (
      Eex (e1, s, Enot (Enot (e2, _), _), _), _), _) ->
       Out.mk_existsc (trexpr e1) (trexpr e2)
    | Enot (Enot (Eapp ("=", [e1;e2], _), _), _) ->
       Out.mk_eqc (trexpr e1) (trexpr e2)
    | Evar (v, _) when Mltoll.is_meta v ->
       Out.mk_anyterm
    | Evar (v, _) ->
       Out.mk_var v
    | Eapp ("$string", [Evar (v, _)], _) ->
       Out.mk_var ("S"^v)
    | Eapp ("$string", _, _) -> assert false
    | Eapp ("=", [e1;e2], _) ->
       Out.mk_eq (trexpr e1) (trexpr e2)
    | Eapp (s, args, _) ->
       Out.mk_app (Out.mk_var s) (List.map trexpr args)
    | Enot (e, _) ->
       Out.mk_not (trexpr e)
    | Eand (e1, e2, _) ->
       Out.mk_and (trexpr e1) (trexpr e2)
    | Eor (e1, e2, _) ->
       Out.mk_or (trexpr e1) (trexpr e2)
    | Eimply (e1, e2, _) ->
       Out.mk_imply (trexpr e1) (trexpr e2)
    | Etrue -> Out.mk_true
    | Efalse -> Out.mk_false
    | Eall (e1, s, e2, _) ->
       Out.mk_forall (trexpr e1) (trexpr e2)
    | Eex (e1, s, e2, _) ->
       Out.mk_exists (trexpr e1) (trexpr e2)
    | Elam _ | Eequiv _ | Emeta _ | Etau _ -> assert false

  type result =
    | Typ of Out.term
    | Indirect of string

  let predefined = ["="; "$string"]

(* returns the list of free variables in phrases *)
  let rec get_freevars ps =
    let symtbl = (Hashtbl.create 97 : (string, int * result) Hashtbl.t) in
    let add_sig sym arity kind =
      if not (Hashtbl.mem symtbl sym) then
        Hashtbl.add symtbl sym (arity, kind)
    in
    let rec get_sig t env e =
      match e with
      | Evar (s, _) -> if not (List.mem s env) then add_sig s 0 t
      | Emeta  _ | Etrue | Efalse -> ()
      | Eapp ("$string", [Evar (s, _)], _) ->
         add_sig ("S"^s) 0 (Typ Out.mk_termtype)
      | Eapp (s, args, _) ->
         add_sig s (List.length args) t;
        List.iter (get_sig (Typ Out.mk_termtype) env) args;
      | Eand (e1, e2, _) | Eor (e1, e2, _)
      | Eimply (e1, e2, _) | Eequiv (e1, e2, _)
        -> get_sig (Typ Out.mk_proptype) env e1;
	  get_sig (Typ Out.mk_proptype) env e2
      | Enot (e1, _) -> get_sig (Typ Out.mk_proptype) env e1;
      | Eall (Evar (v, _), _, e1, _) | Eex (Evar (v, _), _, e1, _)
        -> get_sig (Typ Out.mk_proptype) (v::env) e1
      | Eex _ | Eall _ | Etau _ | Elam _ -> assert false
    in
    let do_phrase p =
      match p with
      | Phrase.Hyp (name, e, _) ->
         get_sig (Typ Out.mk_proptype) [] e;
      | Phrase.Def (DefReal ("", s, _, e, None)) ->
         get_sig (Indirect s) [] e;
      | _ -> assert false
    in
    List.iter do_phrase ps;
    let rec follow_indirect path s =
      if List.mem s path then Out.mk_proptype else
        begin try
                match Hashtbl.find symtbl s with
	        | (_, Typ t) -> t
	        | (_, Indirect s1) -> follow_indirect (s::path) s1
          with Not_found -> Out.mk_proptype
        end
    in
    let rec add_arrow n ty =
      if n = 0 then ty else
        Out.mk_arrow Out.mk_termtype (add_arrow (n-1) ty) in
    let find_sig sym (arity, kind) l =
      if List.mem sym predefined then l
      else
        let ty =
	  match kind with
	  | Typ t -> t
	  | Indirect s -> follow_indirect [] s in
        (sym, add_arrow arity ty) :: l
    in
    Hashtbl.fold find_sig symtbl []

  let rec get_distincts distincts e =
    match e with
    | Eapp ("$string", [Evar (s, _)], _) ->
       if not (List.mem_assoc e distincts)
       then (e, (List.length distincts) + 1) :: distincts
       else distincts
    | _ -> distincts

  let get_all (hyps, defs, distincts) p =
    match p with
    | Phrase.Hyp (name, e, _) when name = goal_name ->
       (hyps, defs, get_distincts distincts e)
    | Phrase.Hyp (name, e, _) ->
       (e :: hyps, defs, get_distincts distincts e)
    | Phrase.Def (DefReal (_, sym, params, body, None)) ->
       (hyps, (sym, (params, body)) :: defs, get_distincts distincts body)
    | Phrase.Def (DefReal (_, sym, params, body, Some _)) -> assert false
    | Phrase.Def (DefPseudo (_, _, _, _)) -> assert false
    | Phrase.Def (DefRec (_, _, _, _)) -> assert false
    | Phrase.Sig _ -> assert false
    | Phrase.Inductive _ -> assert false      (* TODO: to implement *)

  let get_declarations freevars =
    List.map (fun (sym, ty) -> (Out.mk_decl (LjToDk.trexpr (evar sym)) ty)) freevars

  let rec get_rewritings freevars phrases =
    match phrases with
    | Phrase.Def (DefReal ("", sym, params, body, None)) :: ps ->
       let vars, types =
         List.split
	   (List.map
	      (fun e -> match e with
	      | Evar (v, _) -> let t = List.assoc v freevars in LjToDk.trexpr e, t
	      | _ -> assert false) params) in
       Out.mk_rewrite (List.combine vars types)
         (Out.mk_app (Out.mk_var sym) vars) (LjToDk.trexpr body)
       :: (get_rewritings freevars ps)
    | p :: ps -> get_rewritings freevars ps
    | [] -> []

  let rec get_distinctshyps l =
    match l with
    | (x, n) :: (y, m) :: l ->
       enot (eapp ("=", [y; x])) :: (get_distinctshyps ((x, n) :: l))
       @ (get_distinctshyps ((y, m) :: l))
    | _ -> []

  let modname name =
    let buf = Buffer.create (2*String.length name) in
    String.iter
      (fun c -> match c with
      | 'a'..'z' | 'A'..'Z' | '0'..'9' -> Buffer.add_char buf c
      | '_' -> Buffer.add_string buf "__"
      | _ -> Buffer.add_string buf ("_"^(string_of_int (int_of_char c)))) name;
    Buffer.add_string buf "todk";
    Buffer.contents buf

  let rec get_goal phrases =
    match phrases with
    | [] -> None
    | Phrase.Hyp (name, e, _) :: _ when name = goal_name -> Some e
    | _ :: t -> get_goal t

  let get_env phrases lems = 
    let definitions = (Hashtbl.create 97 : (string, Expr.expr list * Expr.expr) Hashtbl.t) in
    let lemmas = (Hashtbl.create 97 : (string, prooftree) Hashtbl.t) in
    List.iter (fun lem -> Hashtbl.add lemmas lem.name lem.proof) lems;
    let hyps, defs, distincts = List.fold_left get_all ([], [], []) phrases in
    List.iter (fun (var, body) -> Hashtbl.add definitions var body) defs;
    let distinctshyps = get_distinctshyps distincts in
    {Lltolj.hypotheses = List.map (Lltolj.use_defs definitions) (distinctshyps@hyps); 
     Lltolj.definitions = definitions;
     Lltolj.lemmas = lemmas;
     Lltolj.distincts = List.map 
	(fun (e, n) -> Lltolj.use_defs definitions e, n) distincts}


  let output oc phrases ppphrases llp filename contextoutput =
    let goal = get_goal phrases in
    let thm, lemmas =
      match List.rev llp with
      | [] -> assert false
      | thm :: lemmas -> thm, lemmas in
    if contextoutput
    then
      begin
        Out.print_line oc (Out.mk_prelude (modname filename));
        let freevars = get_freevars phrases in
        List.iter (Out.print_line oc) (get_declarations freevars);
        List.iter (Out.print_line oc) (get_rewritings freevars phrases);
      end;
    let env = get_env phrases lemmas in
    let ljproof, ljconc = Lltolj.lltolj env thm.proof goal in
    let term = LjToDk.trproof (ljproof, ljconc, []) in
    let rec line =
      Out.mk_deftype (Out.mk_var "conjecture_proof")
        (Out.mk_prf (LjToDk.trexpr ljconc)) term in
    Out.print_line oc line
end

module TranslateDk = Translate(Dkterm)
module TranslateCoq = Translate(ClassicalCoqTerm)

let output = TranslateDk.output
let coq_output = TranslateCoq.output

