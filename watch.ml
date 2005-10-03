(*  Copyright 2005 INRIA  *)
Version.add "$Id: watch.ml,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $";;

open Printf;;

open Expr;;
open Mlproof;;

type item =
  | Hyp of expr
  | Def of string
;;

module HashedItem = struct
  type t = item;;
  let equal i1 i2 =
    match i1, i2 with
    | Hyp h1, Hyp h2 -> Expr.equal h1 h2
    | Def s1, Def s2 -> s1 = s2
    | _, _ -> false
  ;;
  let hash i =
    match i with
    | Hyp h -> Expr.hash h
    | Def s -> Hashtbl.hash s
  ;;
end;;

module HI = Hashtbl.Make (HashedItem);;

let used = (HI.create 97 : unit HI.t);;
let test i = HI.mem used i;;
let add i = if test i then () else HI.add used i ();;

let add_def p =
  match p.mlrule with
  | Definition (DefReal (s, _, _), _, _) -> add (Def s)
  | Definition (DefPseudo ((e, _), _, _, _), _, _) -> add (Hyp e)
  | _ -> ()
;;

let check phr =
  match phr with
  | Phrase.Hyp (name, e, _) when not (test (Hyp e)) ->
      Error.warn (sprintf "unused hypothesis %s" name);
  | Phrase.Def (DefReal (s, _, _)) when not (test (Def s)) ->
      Error.warn (sprintf "unused definition %s" s);
  | _ -> ()
;;

let warn deps prf =
  if !Globals.warnings_flag && deps <> [] then begin
    HI.clear used;
    List.iter (fun e -> add (Hyp e)) prf.mlconc;
    Mlproof.iter add_def prf;
    List.iter check deps;
  end
;;
