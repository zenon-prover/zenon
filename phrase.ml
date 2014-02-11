(*  Copyright 2004 INRIA  *)
Version.add "$Id$";;

open Expr;;


type inductive_arg =
  | Param of string
  | Self
;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
  | Sig of string * string list * string
  | Inductive of
     string * string list * (string * inductive_arg list) list * string
  | Rew of string * expr * int
;;

type zphrase =
  | Zhyp of string * expr * int
  | Zdef of definition
  | Zsig of string * string list * string
  | Zinductive of
     string * string list * (string * inductive_arg list) list * string
  | Zinclude of string
;;

exception Bad_arg;;

let extract_args l =
  List.map (function Evar _ as v -> v | _ -> raise Bad_arg) l
;;

let rec no_duplicates = function
  | [] | [ _ ] -> true
  | h1 :: h2 :: t -> h1 <> h2 && no_duplicates (h2 :: t)
;;

let check_args env args =
  try
    let arg = extract_args args in
    let senv = List.sort compare env in
    let sarg = List.sort compare arg in
    senv = sarg && no_duplicates senv
  with Bad_arg -> false
;;

let rec check_body env s e =
  match e with
  | Evar (v, _) -> v <> s || List.mem e env
  | Emeta _ -> assert false
  | Eapp (ss, args, _) -> ss <> s && List.for_all (check_body env s) args
  | Enot (f, _) -> check_body env s f
  | Eand (f1, f2, _) | Eor (f1, f2, _) | Eimply (f1, f2, _) | Eequiv (f1, f2, _)
    -> check_body env s f1 && check_body env s f2
  | Etrue | Efalse
    -> true
  | Eall (v, _, f, _) | Eex (v, _, f, _)
  | Etau (v, _, f, _) | Elam (v, _, f, _)
    -> check_body (v::env) s f
;;

let rec is_def predef env e =
  match e with
  | Eall (v, t, f, _) -> is_def predef (v::env) f
  | Eequiv (Eapp (s, args, _), body, _) when not (List.mem s predef) ->
     check_args env args && check_body [] s body
  | Eequiv (body, Eapp (s, args, _), _) when not (List.mem s predef) ->
     check_args env args && check_body [] s body
  | Eequiv (Evar (s, _), body, _) when not (List.mem s predef) ->
     env = [] && check_body [] s body
  | Eequiv (body, Evar (s, _), _) when not (List.mem s predef) ->
     env = [] && check_body [] s body
  | Eapp ("=", [Evar (s, _); body], _) when not (List.mem s predef) ->
     env = [] && check_body [] s body
  | Eapp ("=", [body; Evar (s, _)], _) when not (List.mem s predef) ->
     env = [] && check_body [] s body
  | Eapp ("=", [Eapp (s, args, _); body], _) when not (List.mem s predef) ->
     check_args env args && check_body [] s body
  | Eapp ("=", [body; Eapp (s, args, _)], _) when not (List.mem s predef) ->
     check_args env args && check_body [] s body
  | _ -> false
;;

let rec make_def predef orig env e =
  match e with
  | Eall (v, t, f, _) -> make_def predef orig (v::env) f
  | Eequiv (Eapp (s, args, _), body, _)
    when not (List.mem s predef) && check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | Eequiv (body, Eapp (s, args, _), _) when
    not (List.mem s predef) && check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | Eequiv (Evar (s, _), body, _) when not (List.mem s predef) ->
      DefPseudo (orig, s, [], body)
  | Eequiv (body, Evar (s, _), _) when not (List.mem s predef) ->
      DefPseudo (orig, s, [], body)
  | Eapp ("=", [Evar (s, _); body], _) when not (List.mem s predef) ->
      DefPseudo (orig, s, [], body)
  | Eapp ("=", [body; Evar (s, _)], _) when not (List.mem s predef) ->
      DefPseudo (orig, s, [], body)
  | Eapp ("=", [Eapp (s, args, _); body], _)
    when not (List.mem s predef) && check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | Eapp ("=", [body; Eapp (s, args, _)], _)
    when not (List.mem s predef) && check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | _ -> assert false
;;

let rec free_syms env accu e =
  match e with
  | Evar (v, _) -> if List.mem e env then accu else v :: accu
  | Emeta _ -> assert false
  | Eapp (s, args, _) -> List.fold_left (free_syms env) (s::accu) args
  | Enot (f, _) -> free_syms env accu f
  | Eand (f, g, _) -> free_syms env (free_syms env accu f) g
  | Eor (f, g, _) -> free_syms env (free_syms env accu f) g
  | Eimply (f, g, _) -> free_syms env (free_syms env accu f) g
  | Eequiv (f, g, _) -> free_syms env (free_syms env accu f) g
  | Etrue | Efalse -> accu
  | Eall (v, t, f, _)
  | Eex (v, t, f, _)
  | Etau (v, t, f, _)
  | Elam (v, t, f, _)
    -> free_syms (v::env) accu f
;;

let extract_dep = function
  | DefPseudo (_, s, args, body) -> (s, free_syms args [] body)
  | _ -> assert false
;;

let rec follow_deps l deps =
  match l with
  | [] -> []
  | h::t ->
      begin try
        let hl = List.assoc h deps in
        hl @ follow_deps t deps
      with Not_found -> follow_deps t deps
      end
;;

let rec looping (s, l) deps =
  if l = [] then false else
  List.mem s l || looping (s, (follow_deps l deps)) deps
;;

let rec is_redef d ds =
  match d, ds with
  | _, [] -> false
  | _, (DefReal _ :: t) -> is_redef d t
  | _, (DefRec _ :: t) -> is_redef d t
  | DefPseudo (_, s1, _, _), (DefPseudo(_, s2, _, _) :: t) ->
      s1 = s2 || is_redef d t
  | DefReal _, _ -> assert false
  | DefRec _, _ -> assert false
;;

let rec remove_def accu sym defs =
  match defs with
  | [] -> assert false
  | DefPseudo (orig, s, _, _) :: t when s = sym -> (accu @ t, orig)
  | h::t -> remove_def (h::accu) sym t
;;

let get_symbol = function
  | DefPseudo (_, s, _, _) -> s
  | _ -> assert false
;;

let rec xseparate predef deps multi defs hyps l =
  match l with
  | [] -> (List.rev defs, List.rev hyps)
  | Def d :: t -> xseparate predef deps multi (d :: defs) hyps t
  | Hyp (_, e, p) :: t when is_def predef [] e ->
      let d = make_def predef (e, p) [] e in
      let sym = get_symbol d in
      let newdep = extract_dep d in
      if List.mem sym multi || looping newdep deps then
        xseparate predef deps multi defs ((e, p) :: hyps) t
      else if is_redef d defs then
        let (ndefs, ep2) = remove_def [] sym defs in
        xseparate predef (List.remove_assoc sym deps) (sym::multi) ndefs
                  ((e, p) :: ep2 :: hyps) t
      else
        xseparate predef (newdep :: deps) multi (d :: defs) hyps t
  | Hyp (_, e, p) :: t -> xseparate predef deps multi defs ((e, p) :: hyps) t
  | Sig _ :: t -> xseparate predef deps multi defs hyps t
  | Inductive _ :: t -> xseparate predef deps multi defs hyps t
  | Rew _ :: t -> xseparate predef deps multi defs hyps t
;;

let separate predef l = xseparate predef [] [] [] [] l;;

let change_to_def predef body =
  if is_def predef [] body then begin
    match make_def predef (body, 0) [] body with
    | DefPseudo (_, s, args, def) -> DefReal ("", s, args, def, None)
    | _ -> assert false
  end else begin
    raise (Invalid_argument "change_to_def")
  end
;;


let rec test_fv l1 l2 = 
  match l2 with 
  | [] -> true
  | h :: tl when List.mem h l1 -> test_fv l1 tl
  | _ -> false
;;

let rec find_first_sym t = 
  match t with 
    | Evar (sym, _) -> sym
    | Eapp (sym, _, _) -> sym
    | Enot (p1, _) -> find_first_sym p1
    | _ -> assert false
;;

let is_literal_noteq body = 
  match body with 
  | Eapp(sym, _, _) when sym <> "=" -> true
  | Enot(Eapp(sym, _, _), _) when sym <> "=" -> true
  | _ -> false
;;

let is_literal_eq body = 
  match body with 
  | Eapp(sym, _, _)  -> true
  | Enot(Eapp(sym, _, _), _)  -> true
  | _ -> false
;;

let add_rule_term t1 t2 = 
  let sym = find_first_sym t1 in 
  Hashtbl.add !Expr.tbl_term sym (t1, t2)
;;

let add_rule_prop t1 t2 = 
  let sym = find_first_sym t1 in 
  Hashtbl.add !Expr.tbl_prop sym (t1, t2)
;;

(* let rec parse_equal_term body = 
      match body with 
      | Eapp ("=", [t1; t2], _) 
	  when test_fv (get_fv t1) (get_fv t2)
	    -> add_rule_term t1 t2
      | Eapp ("=", [t1; t2], _) 
	  when test_fv (get_fv t2) (get_fv t1)
	    -> add_rule_term t2 t1
      | _ -> assert false
;; *)

let rec parse_equal_term body = 
      match body with 
      | Eapp ("=", [t1; t2], _) -> 
	 begin
	   match t1, t2 with
	   | Evar (_, _), Evar (_, _) -> assert false
	   | _, Evar (_, _) when test_fv (get_fv t1) (get_fv t2) 
	     -> add_rule_term t1 t2
	   | Evar (_, _), _ when test_fv (get_fv t2) (get_fv t1)
	     -> add_rule_term t2 t1
	   | _, _ when test_fv (get_fv t1) (get_fv t2) 
	     -> add_rule_term t1 t2
	   | _, _ when test_fv (get_fv t2) (get_fv t1)
	     -> add_rule_term t2 t1
	   | _, _ -> assert false
	 end
      | _ -> assert false
;;

let rec parse_conj_term body = 
  match body with 
  | Eand (e1, e2, _) -> 
    begin 
      parse_conj_term e1;
      parse_conj_term e2;
    end
  | _ -> parse_equal_term body
;;

let rec parse_term_rule body = 
  match body with 
  | Eall (_, _, pred, _) -> parse_term_rule pred
  | _ -> parse_conj_term body
;;

let rec parse_equiv_prop body = 
  if is_literal_noteq body
  then 
    begin
      match body with 
      | Eapp(sym, _, _) as e1 when sym <> "=" -> 
	 add_rule_prop e1 etrue
      | Enot(Eapp(sym, _, _) as e1, _) when sym <> "=" -> 
	 add_rule_prop e1 efalse
      | _ -> assert false
    end
  else
    begin
      match body with 
      | Eequiv (e1, e2, _) 
	   when is_literal_eq e1 
		&& test_fv (get_fv e1) (get_fv e2)
	-> add_rule_prop e1 e2
      | Eequiv (e1, e2, _)
	   when is_literal_eq e2
		&& test_fv (get_fv e2) (get_fv e1)
	-> add_rule_prop e2 e1
      | _ -> assert false
    end
;;

let rec parse_conj_prop body = 
  match body with 
  | Eand (e1, e2, _) -> 
    begin 
      parse_conj_prop e1;
      parse_conj_prop e2;
    end
  | _ -> parse_equiv_prop body
;;

let rec parse_prop_rule body = 
  match body with 
  | Eall (_, _, pred, _) -> parse_prop_rule pred
  | _ -> parse_conj_prop body
;;


let rec parse_rwrt phrases = 
  match phrases with 
    | [] -> ()
    | Rew (name, body, flag) :: tl ->
      begin 
	match flag with 
	| 0 -> 
	  begin 
	    parse_term_rule body;
	    parse_rwrt tl;
	  end 
	| 1 -> 
	  begin 
	    parse_prop_rule body;
	    parse_rwrt tl;
	  end
	    
	| _ -> assert false
      end 
    | Hyp _ :: tl
      -> parse_rwrt tl
    | Def _ :: tl
      -> parse_rwrt tl
    | Sig _ :: tl 
      -> parse_rwrt tl
    | Inductive _ :: tl
      -> parse_rwrt tl
;;




type tpphrase =
  | Include of string * string list option
  | Formula of string * string * expr
  | Annotation of string
;;
