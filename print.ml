(*  Copyright 2004 INRIA  *)
Version.add "$Id: print.ml,v 1.5 2004-05-25 11:45:13 doligez Exp $";;

open Expr;;
open Mlproof;;
open Printf;;

(* Stdout or a file *)
let outc = ref stdout
let set_outc c = outc := c
let get_outc () = !outc
let printf s = fprintf !outc s

let is_letter c = c >= 'A' && c <= 'Z'  ||  c >= 'a' && c <= 'z';;

let print_vartype (v, t) =
  if t = ""
  then printf "%s " v
  else printf "%s:\"%s\" " v t
;;

let rec expr = function
  | Evar (v, _) -> printf "%s" v;
  | Emeta (e, _) -> printf "_Z%d" (Index.get_number e);
  | Eapp (s, es, _) ->
      printf "(%s" s; List.iter (fun x -> printf " "; expr x) es; printf ")";
  | Enot (e, _) -> printf "(-. "; expr e; printf ")";
  | Eand (e1, e2, _) ->
      printf "(/\\ "; expr e1; printf " "; expr e2; printf ")";
  | Eor (e1, e2, _) ->
      printf "(\\/ "; expr e1; printf " "; expr e2; printf ")";
  | Eimply (e1, e2, _) ->
      printf "(=> "; expr e1; printf " "; expr e2; printf ")";
  | Eequiv (e1, e2, _) ->
      printf "(<=> "; expr e1; printf " "; expr e2; printf ")";
  | Etrue -> printf "(True)";
  | Efalse -> printf "(False)";
  | Eall (v, "", e, _) ->
      printf "(A. ((%s) " v; expr e; printf "))";
  | Eall (v, t, e, _) ->
      printf "(A. ((%s \"%s\") " v t; expr e; printf "))";
  | Eex (v, "", e, _) ->
      printf "(E. ((%s) " v; expr e; printf "))";
  | Eex (v, t, e, _) ->
      printf "(E. ((%s \"%s\") " v t; expr e; printf "))";
  | Etau (v, "", e, _) ->
      printf "(t. ((%s) " v; expr e; printf "))";
  | Etau (v, t, e, _) ->
      printf "(t. ((%s \"%s\") " v t; expr e; printf "))";
;;

let rec expr_soft = function
  | Evar (v, _) -> printf "%s" v;
  | Emeta (e, _) -> printf "Z_%d" (Index.get_number e);
  | Eapp (s, [e1; e2], _) when s <> "" && not (is_letter s.[0]) ->
      printf "("; expr_soft e1; printf " %s " s; expr_soft e2; printf ")";
  | Eapp (s, es, _) ->
      printf "(%s" s;
      List.iter (fun x -> printf " "; expr_soft x) es;
      printf ")";
  | Enot (Eapp ("=", [e1; e2], _), _) ->
      printf "("; expr_soft e1; printf " != "; expr_soft e2; printf ")";
  | Enot (e, _) -> printf "(-. "; expr_soft e; printf ")";
  | Eand (e1, e2, _) ->
      printf "("; expr_soft e1; printf " /\\ "; expr_soft e2; printf ")";
  | Eor (e1, e2, _) ->
      printf "("; expr_soft e1; printf " \\/ "; expr_soft e2; printf ")";
  | Eimply (e1, e2, _) ->
      printf "("; expr_soft e1; printf " => "; expr_soft e2; printf ")";
  | Eequiv (e1, e2, _) ->
      printf "("; expr_soft e1; printf " <=> "; expr_soft e2; printf ")";
  | Etrue -> printf "True";
  | Efalse -> printf "False";
  | Eall (v, "", e, _) ->
      printf "(All %s, " v; expr_soft e; printf ")";
  | Eall (v, t, e, _) ->
      printf "(All %s:%s, " v t; expr_soft e; printf ")";
  | Eex (v, "", e, _) ->
      printf "(Ex %s, " v; expr_soft e; printf ")";
  | Eex (v, t, e, _) ->
      printf "(Ex %s:%s, " v t; expr_soft e; printf ")";
  | Etau _ as e ->
      printf "T_%d" (Index.get_number e);
;;

let phrase = function
  | Phrase.Hyp (e, p) -> printf "$%d " p; expr e; printf "\n";
  | Phrase.Def (DefReal (s, args, e)) ->
      printf "$def %s (" s;
      List.iter (fun x -> printf " %s" x) args;
      printf ") ";
      expr e;
      printf "\n";
  | Phrase.Def (DefPseudo ((hyp, prio), s, args, e)) ->
      printf "#pseudo-def: ";
      expr hyp;
      printf "\n$def %s (" s;
      List.iter (fun x -> printf " %s" x) args;
      printf ") ";
      expr e;
      printf "\n";
;;

let sequent l =
  List.iter (fun x -> expr x; printf " ") l;
;;

let get_rule_name = function
  | Close1 e -> "EqRefl", [e]
  | Close2 e -> "Axiom", [e]
  | False -> "False", []
  | NotTrue -> "NotTrue", []
  | NotNot (e) -> "NotNot", [e]
  | NotAll (e) -> "NotAll", [e]
  | Ex (e) -> "Exists", [e]
  | NotEqual (e1, e2) -> "NotEqual", [e1; e2]
  | And (e1, e2) -> "And", [e1; e2]
  | NotOr (e1, e2) -> "NotOr", [e1; e2]
  | NotImpl (e1, e2) -> "NotImply", [e1; e2]
  | All (e1, e2) -> "All", [e1; e2]
  | NotEx (e1, e2) -> "NotExists", [e1; e2]
  | Or (e1, e2) -> "Or", [e1; e2]
  | Impl (e1, e2) -> "Imply", [e1; e2]
  | NotAnd (e1, e2) -> "NotAnd", [e1; e2]
  | Equiv (e1, e2) -> "Equiv", [e1; e2]
  | NotEquiv (e1, e2) -> "NotEquiv", [e1; e2]
  | P_NotP (e1, e2) -> "P-NotP", [e1; e2]
  | Equal_NotEqual (e1, e2, e3, e4) -> "Eq-NotEq", [e1; e2; e3; e4]
  | Definition (DefReal (s, _, _), e, _) -> "Definition("^s^")", [e]
  | Definition (DefPseudo (_, s, _, _), e, _) -> "Definition-Pseudo("^s^")", [e]
  | ConjTree e -> "ConjTree", [e]
  | DisjTree e -> "DisjTree", [e]
  | AllPartial (e1, e2) -> "All-Partial", [e1; e2]
  | NotExPartial (e1, e2) -> "NotEx-Partial", [e1; e2]
  | CloseEq (e1, e2) -> "EqSym", [e1; e2]
  | Ext (th, ru, args) -> ("Extension/"^th^"/"^ru), args
;;

let mlproof_rule r =
  let rname, args = get_rule_name r in
  printf "%s" rname;
  List.iter (fun e -> printf ", "; expr e) args;
;;

let mlproof_rule_soft r =
  let rname, args = get_rule_name r in
  printf "%s" rname;
  List.iter (fun e -> printf ", "; expr_soft e) args;
;;

let mlrule_short r =
  let rname, args = get_rule_name r in
  printf "%s" rname;
;;

let cur_step = ref 0;;
let new_step () = incr cur_step; !cur_step;;

let rec mlproof_aux p =
  if p.mlrefc < 1 then
    - p.mlrefc
  else begin
    let subs = Array.map mlproof_aux p.mlhyps in
    let n = new_step () in
    printf "%d. " n;
    sequent p.mlconc;
    printf "  ### ";
    mlrule_short p.mlrule;
    Array.iter (fun x -> printf " %d" x) subs;
    printf "\n";
    p.mlrefc <- -n;
    n
  end
;;

let mlproof p = ignore (mlproof_aux p);;

let hlrule_name = function
  | Close1 (e) -> "EqRefl", [enot (eapp ("=", [e; e]))]
  | Close2 (e) -> "Axiom", [e; enot (e)]
  | False -> "False", []
  | NotTrue -> "NotTrue", []
  | NotNot (e) -> "NotNot", [enot (enot (e))]
  | And (e1, e2) -> "And", [eand (e1, e2)]
  | NotOr (e1, e2) -> "NotOr", [enot (eor (e1, e2))]
  | NotImpl (e1, e2) -> "NotImply", [enot (eimply (e1, e2))]
  | NotAll (e) -> "NotAll", [e]
  | Ex (e) -> "Exists", [e]
  | All (e1, e2) -> "All", [e1]
  | NotEx (e1, e2) -> "NotExists", [e1]
  | Or (e1, e2) -> "Or", [eor (e1, e2)]
  | Impl (e1, e2) -> "Imply", [eimply (e1, e2)]
  | NotAnd (e1, e2) -> "NotAnd", [enot (eand (e1, e2))]
  | Equiv (e1, e2) -> "Equiv", [eequiv (e1, e2)]
  | NotEquiv (e1, e2) -> "NotEquiv", [enot (eequiv (e1, e2))]
  | Equal_NotEqual (e1, e2, e3, e4) ->
      "Eq-NotEq", [eapp ("=", [e1; e2]); enot (eapp ("=", [e3; e4]))]
  | P_NotP (e1, e2) -> "P-NotP", [e1; e2]
  | NotEqual (e1, e2) -> "NotEqual", [enot (eapp ("=", [e1; e2]))]
  | Definition ((DefReal (s, _, _) | DefPseudo (_, s, _, _)), e, _) ->
      "Definition("^s^")", [e]
  | ConjTree (e) -> "ConjTree", [e]
  | DisjTree (e) -> "DisjTree", [e]
  | AllPartial (e1, e2) -> "All", [e1]
  | NotExPartial (e1, e2) -> "NotExists", [e1]
  | CloseEq (e1, e2) ->
      "EqSym", [eapp ("=", [e1; e2]); enot (eapp ("=", [e2; e1]))]
  | Ext (th, ru, args) -> ("Extension/"^th^"/"^ru), args
;;

let hlrule r =
  let rname, args = hlrule_name r in
  printf "[%s" rname;
  List.iter (fun x -> printf " H%d" (Index.get_number x)) args;
  printf "]";
;;

let rec vertical_sequent ctx fms =
  match fms with
  | [] -> ()
  | h :: t ->
      if List.exists (Expr.equal h) ctx
      then vertical_sequent ctx t
      else begin
        printf "H%d: " (Index.get_number h);
        expr_soft h;
        printf "\n      ";
        vertical_sequent ctx t;
      end;
;;


let rec xhlproof chaining depth ctx n p =
  if p.mlrefc < 1 then begin
    if (not chaining) then printf "\n";
    printf "%4d. see %d\n" n (- p.mlrefc);
  end else if depth >= 0 then begin
    match p.mlrule with
    | And _ | NotOr _ | NotImpl _ | NotAll _ | Ex _ | ConjTree _
    | AllPartial _ | NotExPartial _ | Definition _ ->
        assert (Array.length p.mlhyps = 1);
        xhlproof chaining depth ctx n p.mlhyps.(0)
    | _ ->
        if (not chaining) then printf "\n";
        printf "%4d. " n;
        vertical_sequent ctx p.mlconc;
        let subs = Array.map (fun _ -> new_step ()) p.mlhyps in
        printf "### ";
        if depth = 0 && subs <> [| |] then begin
          printf "...proof-omitted...\n";
          Array.iter (xhlproof true (depth-1) ctx n) p.mlhyps;
        end else begin
          hlrule p.mlrule;
          if subs <> [| |] then printf " -->";
          Array.iter (fun x -> printf " %d" x) subs;
          printf "\n";
          for i = 0 to Array.length p.mlhyps - 1 do
            xhlproof (i = 0) (depth-1) p.mlconc subs.(i) p.mlhyps.(i);
          done;
        end;
        p.mlrefc <- -n;
  end
;;

let hlproof depth p = ignore (xhlproof true depth [] (new_step ()) p);;

open Llproof;;

let indent i = for j = 0 to i do printf "  "; done;;

let rec llproof_term = function
  | Evar (v, _) -> printf "%s" v;
  | Eapp (s, [e1; e2], _) when s <> "" && not (is_letter s.[0]) ->
      printf "("; llproof_term e1; printf " %s " s; llproof_term e2; printf ")";
  | Eapp (s, args, _) -> printf "%s(" s; llproof_term_list args; printf ")";
  | _ -> assert false

and llproof_term_list = function
  | [] -> ()
  | [t] -> llproof_term t;
  | t::ts -> llproof_term t; printf ", "; llproof_term_list ts;
;;

let rec llproof_prop = function
  | Efalse -> printf "false";
  | Etrue -> printf "true";
  | Enot (p, _) -> printf "~"; llproof_prop p;
  | Eand (p1, p2, _) ->
      printf "("; llproof_prop p1; printf " /\\ "; llproof_prop p2; printf ")";
  | Eor (p1, p2, _) ->
      printf "("; llproof_prop p1; printf " \\/ "; llproof_prop p2; printf ")";
  | Eimply (p1, p2, _) ->
      printf "("; llproof_prop p1; printf " => "; llproof_prop p2; printf ")";
  | Eequiv (p1, p2, _) ->
      printf "("; llproof_prop p1; printf " <=> "; llproof_prop p2; printf ")";
  | Eall (v, "", p, _) -> printf "All %s, " v; llproof_prop p;
  | Eex (v, "", p, _) -> printf "Ex %s, " v; llproof_prop p;
  | Eall (v, t, p, _) -> printf "All %s:%s, " v t; llproof_prop p;
  | Eex (v, t, p, _) -> printf "Ex %s:%s, " v t; llproof_prop p;
  | Eapp ("=", [t1; t2], _) ->
      printf "("; llproof_term t1; printf " = "; llproof_term t2; printf ")";
  | Eapp (s, [], _) -> printf "%s" s;
  | Eapp (s, args, _) -> printf "%s(" s; llproof_term_list args; printf ")";

  | Evar _
  | Emeta _
  | Etau _
    -> assert false;
;;

let binop_name = function
  | And -> "And"
  | Or -> "Or"
  | Imply -> "Imply"
  | Equiv -> "Equiv"
;;

let llproof_rule = function
  | Rfalse -> printf "---false";
  | Rnottrue -> printf "---nottrue";
  | Raxiom (p) -> printf "---axiom "; llproof_prop p;
  | Rnoteq (t) -> printf "---noteq "; llproof_term t;
  | Rnotnot (p) -> printf "---notnot "; llproof_prop p;
  | Rconnect (op, p, q) ->
      printf "---connect (%s, " (binop_name op);
      llproof_prop p;
      printf ", ";
      llproof_prop q;
      printf ")";
  | Rnotconnect (op, p, q) ->
      printf "---notconnect ~(%s, " (binop_name op);
      llproof_prop p;
      printf ", ";
      llproof_prop q;
      printf ")";
  | Rex (p, v) -> printf "---ex ("; llproof_prop p; printf ", %s)" v;
  | Rall (p, t) ->
      printf "---all (";
      llproof_prop p;
      printf ", ";
      llproof_term t;
      printf ")";
  | Rnotex (p, t) ->
      printf "---notex (";
      llproof_prop p;
      printf ", ";
      llproof_term t;
      printf ")";
  | Rnotall (p, v) -> printf "---notall ("; llproof_prop p; printf ", %s)" v;
  | Rpnotp (p, q) ->
      printf "---pnotp (";
      llproof_prop p;
      printf ", ";
      llproof_prop q;
      printf ")";
  | Rnotequal (t, u) ->
      printf "---notequal (";
      llproof_term t;
      printf ", ";
      llproof_term u;
      printf ")";
  | Requalnotequal (t0, t1, t2, t3) ->
      printf "---equalnotequal (";
      llproof_term t0;
      printf ", ";
      llproof_term t1;
      printf ", ";
      llproof_term t2;
      printf ", ";
      llproof_term t3;
      printf ")";
  | Rlemma (name, args) ->
      printf "---lemma %s [ " name;
      List.iter (fun x -> printf "%s " x) args;
      printf "]";
  | Rdefinition (folded, unfolded) ->
      printf "---definition";
;;

let nodes = ref 0;;

let rec llproof_tree i t =
  let prop_space p = llproof_prop p; printf "   "; in
  indent i; List.iter prop_space t.conc; printf "\n";
  indent i; llproof_rule t.rule; printf "\n";
  List.iter (llproof_tree (i+1)) t.hyps;
  incr nodes;
;;

let llproof_lemma {name=name; params=params; proof=tree} =
  printf "%s" name;
  if params <> [] then begin
    printf " [";
    List.iter print_vartype params;
    printf "]";
  end;
  printf "\n";
  llproof_tree 1 tree;
  printf "\n";
;;

let llproof p =
  List.iter llproof_lemma p;
;;
