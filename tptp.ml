(*  Copyright 2004 INRIA  *)
Version.add "$Id: tptp.ml,v 1.5 2004-09-09 15:25:35 doligez Exp $";;

open Expr;;
open Phrase;;

(* FIXME a faire: enlever le cas particulier pour l'egalite (?) *)

let x = evar "x" and y = evar "y" and z = evar "z";;

let equality_axioms = [
  eall (x, "", eapp ("=", [x; x]));
  eall (x, "",
    eall (y, "", eimply (eapp ("=", [x; y]), eapp ("=", [y; x]))));
  eall (x, "",
    eall (y, "",
      eall (z, "",
        eimply (eand (eapp ("=", [x; y]),
                      eapp ("=", [y; z])),
                eapp ("=", [x; z])))));
];;

let check_arg context v1 v2 a1 a2 =
  match a1, a2 with
  | Evar (w1, _), Evar (w2, _) ->
      a1 == a2 && List.mem a1 context
      || a1 == v1 && a2 == v2
      || a1 == v2 && a2 == v1
  | _, _ -> false
;;

let rec equ_form context f =
  match f with
  | Eall (v, t, g, _) -> equ_form (v::context) g
  | Eimply (Eapp ("=", [(Evar _ as v1); (Evar _ as v2)], _),
            Eapp ("=", [Eapp (s1, l1, _); Eapp (s2, l2, _)], _), _) ->
      s1 = s2 && List.mem v1 context && List.mem v2 context
      && List.for_all2 (check_arg context v1 v2) l1 l2
  | Eimply (Eand (Eapp ("=", [(Evar _ as v1); (Evar _ as v2)], _),
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

let rec translate dirs ps =
  match ps with
  | [] -> []
  | Include f :: t -> (try_incl dirs f) @ (translate dirs t)
  | Formula (name, "axiom", body) :: t ->
      if is_eq_formula body
      then translate dirs t
      else Hyp (name, body, 2) :: (translate dirs t)
  | Formula (name, "hypothesis", body) :: t ->
      if is_eq_formula body
      then translate dirs t
      else Hyp (name, body, 1) :: (translate dirs t)
  | Formula (name, "conjecture", body) :: t ->
      Hyp ("_Zgoal", enot (body), 0) :: (translate dirs t)
  | Formula (name, k, body) :: t ->
      failwith ("unknown formula kind: " ^ k)

and try_incl dirs f =
  let rec loop = function
    | [] -> failwith (Printf.sprintf "file %s not found in include path" f)
    | h::t -> begin
        try incl dirs (Filename.concat h f)
        with Sys_error _ -> loop t
      end
  in
  loop dirs

and incl dir name =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  let tpphrases = Parser.tpfile Lexer.tptoken lexbuf in
  close_in chan;
  translate dir tpphrases
;;
