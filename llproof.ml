(*  Copyright 2004 INRIA  *)
Version.add "$Id: llproof.ml,v 1.5 2004-05-27 17:21:24 doligez Exp $";;

open Expr;;

type binop =
  | And
  | Or
  | Imply
  | Equiv
;;

type rule =
  | Rfalse
  | Rnottrue
  | Raxiom of expr
  | Rnoteq of expr
  | Rnotnot of expr
  | Rconnect of binop * expr * expr
  | Rnotconnect of binop * expr * expr
  | Rex of expr * string
  | Rall of expr * expr
  | Rnotex of expr * expr
  | Rnotall of expr * string
  | Rpnotp of expr * expr
  | Rnotequal of expr * expr
  | Requalnotequal of expr * expr * expr * expr
  | Rdefinition of expr * expr
  | Rextension of string * expr list * expr list * expr list list
  | Rlemma of string * string list
;;

type prooftree = {
  conc : expr list;
  rule : rule;
  hyps : prooftree list;
};;

type lemma = {
  name : string;                    (* nom du lemme *)
  params : (string * string) list;  (* parametres, avec leurs types *)
  proof : prooftree;                (* preuve *)
};;

type proof = lemma list;;
