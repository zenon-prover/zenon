(*  Copyright 2004 INRIA  *)
Misc.version "$Id: phrase.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $";;

open Expr;;

type phrase =
  | Hyp of expr * int
  | Def of definition
;;

exception Bad_arg;;

let extract_args l =
  List.map (function Evar (v, _) -> v | _ -> raise Bad_arg) l
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

let rec is_def env e =
  match e with
  | Eall (v, t, f, _) -> is_def (v::env) f
  | Eequiv (Eapp (s, args, _), _, _)
  | Eequiv (_, Eapp (s, args, _), _)
    -> check_args env args
  | Eequiv (Evar (s, _), _, _)
  | Eequiv (_, Evar (s, _), _)
    -> env = []
  | Eapp ("=", [Eapp (s, args, _); _], _)
  | Eapp ("=", [_; Eapp (s, args, _)], _)
    -> check_args env args
  | Eapp ("=", [Evar (s, _); _], _)
  | Eapp ("=", [_; Evar (s, _)], _)
    -> env = []
  | _ -> false
;;

let rec make_def orig env e =
  match e with
  | Eall (v, t, f, _) -> make_def orig (v::env) f
  | Eequiv (Eapp (s, args, _), body, _) when check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | Eequiv (body, Eapp (s, args, _), _) when check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | Eequiv (Evar (s, _), body, _) ->
      DefPseudo (orig, s, [], body)
  | Eequiv (body, Evar (s, _), _) ->
      DefPseudo (orig, s, [], body)
  | Eapp ("=", [Eapp (s, args, _); body], _) when check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | Eapp ("=", [body; Eapp (s, args, _)], _) when check_args env args ->
      DefPseudo (orig, s, extract_args args, body)
  | Eapp ("=", [Evar (s, _); body], _) ->
      DefPseudo (orig, s, [], body)
  | Eapp ("=", [body; Evar (s, _)], _) ->
      DefPseudo (orig, s, [], body)
  | _ -> assert false
;;

let rec free_syms env accu e =
  match e with
  | Evar (v, _) -> if List.mem v env then accu else v :: accu
  | Emeta _ -> assert false
  | Eapp (s, args, _) -> List.fold_left (free_syms env) (s::accu) args
  | Enot (f, _) -> free_syms env accu f
  | Eand (f, g, _) -> free_syms env (free_syms env accu f) g
  | Eor (f, g, _) -> free_syms env (free_syms env accu f) g
  | Eimply (f, g, _) -> free_syms env (free_syms env accu f) g
  | Eequiv (f, g, _) -> free_syms env (free_syms env accu f) g
  | Etrue -> accu
  | Efalse -> accu
  | Eall (v, t, f, _) -> free_syms (v::env) accu f
  | Eex (v, t, f, _) -> free_syms (v::env) accu f
  | Etau (v, t, f, _) -> free_syms (v::env) accu f
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

let rec xseparate deps defs hyps l =
  match l with
  | [] -> (List.rev defs, List.rev hyps)
  | Def d :: t -> xseparate deps (d :: defs) hyps t
  | Hyp (e, p) :: t when is_def [] e ->
      let d = make_def e [] e in
      let newdep = extract_dep d in
      if looping newdep deps then
        xseparate deps defs ((e, p) :: hyps) t
      else
        xseparate (newdep :: deps) (d :: defs) hyps t 
  | Hyp (e, p) :: t -> xseparate deps defs ((e, p) :: hyps) t
;;

let separate l = xseparate [] [] [] l;;

type tpphrase =
  | Include of string
  | Clause of string * string * expr list
  | Formula of string * string * expr
;;
