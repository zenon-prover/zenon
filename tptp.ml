(*  Copyright 2004 INRIA  *)
Version.add "$Id: tptp.ml,v 1.3 2004-05-27 17:21:24 doligez Exp $";;

open Expr;;
open Phrase;;

let equality_axioms = [
  eall ("x", "", eapp ("=", [evar "x"; evar "x"]));
  eall ("x", "",
    eall ("y", "", eimply (eapp ("=", [evar "x"; evar "y"]),
                           eapp ("=", [evar "y"; evar "x"]))));
  eall ("x", "",
    eall ("y", "",
      eall ("z", "",
        eimply (eand (eapp ("=", [evar "x"; evar "y"]),
                      eapp ("=", [evar "y"; evar "z"])),
                eapp ("=", [evar "x"; evar "z"])))));
];;

let check_arg context v1 v2 a1 a2 =
  match a1, a2 with
  | Evar (w1, _), Evar (w2, _) ->
      w1 = w2 && List.mem w1 context
      || w1 = v1 && w2 = v2
      || w1 = v2 && w2 = v1
  | _, _ -> false
;;

let rec equ_form context f =
  match f with
  | Eall (v, t, g, _) -> equ_form (v::context) g
  | Eimply (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _),
            Eapp ("=", [Eapp (s1, l1, _); Eapp (s2, l2, _)], _), _) ->
      s1 = s2 && List.mem v1 context && List.mem v2 context
      && List.for_all2 (check_arg context v1 v2) l1 l2
  | Eimply (Eand (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _),
                  Eapp (s1, l1, _), _),
            Eapp (s2, l2, _), _) ->
      s1 = s2 && List.mem v1 context && List.mem v2 context
      && List.for_all2 (check_arg context v1 v2) l1 l2
  | _ -> false
;;

let is_eq_formula f =
  List.exists (Expr.equal f) equality_axioms
  || equ_form [] f
;;

let rec translate dir ps =
  match ps with
  | [] -> []
  | Include f :: t -> (try_incl dir f) @ (translate dir t)
  | Formula (name, "axiom", body) :: t ->
      if is_eq_formula body
      then translate dir t
      else Hyp (name, body, 2) :: (translate dir t)
  | Formula (name, "hypothesis", body) :: t ->
      if is_eq_formula body
      then translate dir t
      else Hyp (name, body, 1) :: (translate dir t)
  | Formula (name, "conjecture", body) :: t ->
      Hyp (name, enot (body), 0) :: (translate dir t)
  | Formula (name, k, body) :: t ->
      raise (Failure ("unknown formula kind: "^k))

and try_incl dir f =
  try
    incl dir (Filename.concat dir f)
  with Sys_error _ ->
    let pp = Filename.parent_dir_name in
    let name = List.fold_left Filename.concat dir [pp; pp; f] in
    incl dir name

and incl dir name =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  let tpphrases = Parser.tpfile Lexer.tptoken lexbuf in
  close_in chan;
  translate dir tpphrases
;;
