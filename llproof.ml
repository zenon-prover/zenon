(*  Copyright 2004 INRIA  *)
Version.add "$Id: llproof.ml,v 1.4 2004-05-25 11:44:05 doligez Exp $";;

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
  | Rlemma of string * string list
  | Rdefinition of expr * expr
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
