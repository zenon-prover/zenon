(*  Copyright 2004 INRIA  *)
Version.add "$Id: print.ml,v 1.12 2005-11-05 11:13:17 doligez Exp $";;

open Expr;;
open Mlproof;;
open Printf;;


type output = Buff of Buffer.t | Chan of out_channel;;

let mybuf = Buffer.create 100;;
let mychan = ref stdout;;
let flush () = Buffer.output_buffer !mychan mybuf; Buffer.clear mybuf;;

let printf = ();; (* FIXME DEBUG *)

let oprintf o fmt (* ... *) =
  match o with
  | Buff b -> bprintf b fmt (* ... *)
  | Chan c ->
     flush ();
     mychan := c;
     bprintf mybuf fmt (* ... *)
;;

let buf o =
  match o with
  | Buff b -> b
  | Chan c -> mybuf
;;

let is_letter c =
  match c with
  | 'A' .. 'Z' | 'a' .. 'z' -> true
  | _ -> false
;;

let print_var b v =
  match v with
  | Evar (s, _) -> bprintf b "%s" s
  | _ -> assert false
;;

let print_vartype b (v, t) =
  if t = ""
  then print_var b v
  else bprintf b "%a:\"%s\" " print_var v t
;;

let rec expr o ex =
  let printf f = oprintf o f in
  match ex with
  | Evar (v, _) -> printf "%s" v;
  | Emeta (m, _) -> printf "X'%d" m;
  | Eapp (s, es, _) ->
      printf "(%s" s; List.iter (fun x -> printf " "; expr o x) es; printf ")";
  | Enot (e, _) -> printf "(-. "; expr o e; printf ")";
  | Eand (e1, e2, _) ->
      printf "(/\\ "; expr o e1; printf " "; expr o e2; printf ")";
  | Eor (e1, e2, _) ->
      printf "(\\/ "; expr o e1; printf " "; expr o e2; printf ")";
  | Eimply (e1, e2, _) ->
      printf "(=> "; expr o e1; printf " "; expr o e2; printf ")";
  | Eequiv (e1, e2, _) ->
      printf "(<=> "; expr o e1; printf " "; expr o e2; printf ")";
  | Etrue -> printf "(True)";
  | Efalse -> printf "(False)";
  | Eall (v, "", e, _, _) ->
      printf "(A. ((%a) " print_var v; expr o e; printf "))";
  | Eall (v, t, e, _, _) ->
      printf "(A. ((%a \"%s\") " print_var v t; expr o e; printf "))";
  | Eex (v, "", e, _, _) ->
      printf "(E. ((%a) " print_var v; expr o e; printf "))";
  | Eex (v, t, e, _, _) ->
      printf "(E. ((%a \"%s\") " print_var v t; expr o e; printf "))";
  | Etau (v, "", e, _) ->
      printf "(t. ((%a) " print_var v; expr o e; printf "))";
  | Etau (v, t, e, _) ->
      printf "(t. ((%a \"%s\") " print_var v t; expr o e; printf "))";
;;

let expr o e =
  expr o e;
  flush ();
;;

let rec expr_soft o ex =
  let printf f = oprintf o f in
  match ex with
  | Evar (v, _) -> printf "%s" v;
  | Emeta (m, _) -> printf "X'%d" m;
  | Eapp (s, [e1; e2], _) when s <> "" && not (is_letter s.[0]) ->
      printf "("; expr_soft o e1; printf " %s " s; expr_soft o e2; printf ")";
  | Eapp (s, es, _) ->
      printf "(%s" s;
      List.iter (fun x -> printf " "; expr_soft o x) es;
      printf ")";
  | Enot (Eapp ("=", [e1; e2], _), _) ->
      printf "("; expr_soft o e1; printf " != "; expr_soft o e2; printf ")";
  | Enot (e, _) -> printf "(-. "; expr_soft o e; printf ")";
  | Eand (e1, e2, _) ->
      printf "("; expr_soft o e1; printf " /\\ "; expr_soft o e2; printf ")";
  | Eor (e1, e2, _) ->
      printf "("; expr_soft o e1; printf " \\/ "; expr_soft o e2; printf ")";
  | Eimply (e1, e2, _) ->
      printf "("; expr_soft o e1; printf " => "; expr_soft o e2; printf ")";
  | Eequiv (e1, e2, _) ->
      printf "("; expr_soft o e1; printf " <=> "; expr_soft o e2; printf ")";
  | Etrue -> printf "True";
  | Efalse -> printf "False";
  | Eall (Evar (v, _), "", e, _, _) ->
      printf "(All %s, " v; expr_soft o e; printf ")";
  | Eall (Evar (v, _), t, e, _, _) ->
      printf "(All %s:%s, " v t; expr_soft o e; printf ")";
  | Eex (Evar (v, _), "", e, _, _) ->
      printf "(Ex %s, " v; expr_soft o e; printf ")";
  | Eex (Evar (v, _), t, e, _, _) ->
      printf "(Ex %s:%s, " v t; expr_soft o e; printf ")";
  | Eall _ | Eex _ -> assert false
  | Etau _ as e ->
      printf "T_%d" (Index.get_number e);
;;

let expr_soft o e =
  expr_soft o e;
  flush ();
;;

let rec print_list b p_elem sep l =
  match l with
  | [] -> ()
  | [e] -> p_elem b e
  | h::t -> p_elem b h; bprintf b "%s" sep; print_list b p_elem sep t
;;

let phrase o ph =
  let pro f = oprintf o f in
  begin match ph with
  | Phrase.Hyp (n, e, p) -> pro "# %s:\n$%d " n p; expr o e; pro "\n";
  | Phrase.Def (DefReal (s, args, e)) ->
      pro "$def %s (" s;
      print_list (buf o) print_var " " args;
      pro ") ";
      expr o e;
      pro "\n";
  | Phrase.Def (DefPseudo ((hyp, prio), s, args, e)) ->
      pro "#pseudo-def: ";
      expr o hyp;
      pro "\n$def %s (" s;
      print_list (buf o) print_var " " args;
      pro ") ";
      expr o e;
      pro "\n";
  | Phrase.Sig (sym, args, res) ->
      pro "$sig %s (" sym;
      List.iter (fun x -> pro " %s" x) args;
      pro ") %s\n" res;
  end;
  flush ();
;;

let sequent o l =
  List.iter (fun x -> expr o x; oprintf o " ") l;
;;

let get_rule_name = function
  | Close e -> "Axiom", [e]
  | Close_refl (s, e) -> "Refl("^s^")", [e]
  | Close_sym (s, e1, e2) -> "Sym("^s^")", [e1; e2]
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
  | P_NotP_sym (s, e1, e2) -> "P-NotP-sym("^s^")", [e1; e2]
  | Definition (DefReal (s, _, _), e, _) -> "Definition("^s^")", [e]
  | Definition (DefPseudo (_, s, _, _), e, _) -> "Definition-Pseudo("^s^")", [e]
  | ConjTree e -> "ConjTree", [e]
  | DisjTree e -> "DisjTree", [e]
  | AllPartial (e1, s, n) -> "All-Partial", [e1]
  | NotExPartial (e1, s, n) -> "NotEx-Partial", [e1]
  | Refl (s, e1, e2) -> "Refl("^s^")", [e1; e2]
  | Trans (e1, e2) -> "Trans", [e1; e2]
  | Trans_sym (e1, e2) -> "Trans_sym", [e1; e2]
  | TransEq (e1, e2, e3) -> "TransEq", [e1; e2; e3]
  | TransEq_sym (e1, e2, e3) -> "TransEq_sym", [e1; e2; e3]
  | Cut (e1) -> "Cut", [e1]
  | Ext (th, ru, args) -> "Extension/"^th^"/"^ru, args
;;

let mlproof_rule o r =
  let rname, args = get_rule_name r in
  oprintf o "%s" rname;
  List.iter (fun e -> oprintf o ", "; expr o e) args;
  flush ();
;;

let mlproof_rule_soft o r =
  let rname, args = get_rule_name r in
  oprintf o "%s" rname;
  let f e =
    oprintf o ", [%d]" (Index.get_number e);
    expr_soft o e;
  in
  List.iter f args;
  flush ();
;;

let mlrule_short o r =
  let rname, args = get_rule_name r in
  oprintf o "%s" rname;
;;

let cur_step = ref 0;;
let new_step () = incr cur_step; !cur_step;;

let rec mlproof_aux o p =
  if p.mlrefc < 1 then
    - p.mlrefc
  else begin
    let subs = Array.map (mlproof_aux o) p.mlhyps in
    let n = new_step () in
    oprintf o "%d. " n;
    sequent o p.mlconc;
    oprintf o "  ### ";
    mlrule_short o p.mlrule;
    Array.iter (fun x -> oprintf o " %d" x) subs;
    oprintf o "\n";
    p.mlrefc <- -n;
    n
  end
;;

let mlproof o p =
  ignore (mlproof_aux o p);
  flush ();
;;

let hlrule_name = function
  | Close (e) -> "Axiom", [e; enot (e)]
  | Close_refl (s, e) -> "Refl("^s^")", [enot (eapp (s, [e; e]))]
  | Close_sym (s, e1, e2) ->
      "Sym("^s^")", [eapp (s, [e1; e2]); enot (eapp (s, [e2; e1]))]
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
  | P_NotP (e1, e2) -> "P-NotP", [e1; e2]
  | P_NotP_sym (s, e1, e2) -> "P-NotP-sym("^s^")", [e1; e2]
  | NotEqual (e1, e2) -> "NotEqual", [enot (eapp ("=", [e1; e2]))]
  | Definition ((DefReal (s, _, _) | DefPseudo (_, s, _, _)), e, _) ->
      "Definition("^s^")", [e]
  | ConjTree (e) -> "ConjTree", [e]
  | DisjTree (e) -> "DisjTree", [e]
  | AllPartial (e1, s, n) -> "All", [e1]
  | NotExPartial (e1, s, n) -> "NotExists", [e1]
  | Refl (s, e1, e2) -> "Refl("^s^")", [enot (eapp (s, [e1; e2]))]
  | Trans (e1, e2) -> "Trans", [e1; e2]
  | Trans_sym (e1, e2) -> "Trans_sym", [e1; e2]
  | TransEq (e1, e2, e3) -> "TransEq", [e1; e2; e3]
  | TransEq_sym (e1, e2, e3) -> "TransEq_sym", [e1; e2; e3]
  | Cut (e1) -> "Cut", [e1]
  | Ext (th, ru, args) -> ("Extension/"^th^"/"^ru), args
;;

let hlrule o r =
  let rname, args = hlrule_name r in
  oprintf o "[%s" rname;
  List.iter (fun x -> oprintf o " H%d" (Index.get_number x)) args;
  oprintf o "]";
;;

let rec vertical_sequent o ctx fms =
  match fms with
  | [] -> ()
  | h :: t ->
      if List.exists (Expr.equal h) ctx
      then vertical_sequent o ctx t
      else begin
        oprintf o "H%d: " (Index.get_number h);
        expr_soft o h;
        oprintf o "\n      ";
        vertical_sequent o ctx t;
      end;
;;


let rec hlproof o chaining depth ctx n p =
  let printf f = oprintf o f in
  if p.mlrefc < 1 then begin
    if (not chaining) then printf "\n";
    printf "%4d. see %d\n" n (- p.mlrefc);
  end else if depth >= 0 then begin
    match p.mlrule with
    | And _ | NotOr _ | NotImpl _ | NotAll _ | Ex _ | ConjTree _
    | AllPartial _ | NotExPartial _ | Definition _ ->
        assert (Array.length p.mlhyps = 1);
        hlproof o chaining depth ctx n p.mlhyps.(0)
    | _ ->
        if (not chaining) then printf "\n";
        printf "%4d. " n;
        vertical_sequent o ctx p.mlconc;
        let subs = Array.map (fun _ -> new_step ()) p.mlhyps in
        printf "### ";
        if depth = 0 && subs <> [| |] then begin
          printf "...proof-omitted...\n";
          Array.iter (hlproof o true (depth-1) ctx n) p.mlhyps;
        end else begin
          hlrule o p.mlrule;
          if subs <> [| |] then printf " -->";
          Array.iter (fun x -> printf " %d" x) subs;
          printf "\n";
          for i = 0 to Array.length p.mlhyps - 1 do
            hlproof o (i = 0) (depth-1) p.mlconc subs.(i) p.mlhyps.(i);
          done;
        end;
        p.mlrefc <- -n;
  end
;;

let hlproof o depth p =
  ignore (hlproof o true depth [] (new_step ()) p);
  flush ();
;;

open Llproof;;

let indent o i = for j = 0 to i do oprintf o "  "; done;;

let rec llproof_term o t =
  let printf f = oprintf o f in
  match t with
  | Evar (v, _) -> printf "%s" v;
  | Eapp (s, [e1; e2], _) when s <> "" && not (is_letter s.[0]) ->
      printf "(";
      llproof_term o e1;
      printf " %s " s;
      llproof_term o e2;
      printf ")";
  | Eapp (s, args, _) -> printf "%s(" s; llproof_term_list o args; printf ")";
  | _ -> assert false

and llproof_term_list o l =
  match l with
  | [] -> ()
  | [t] -> llproof_term o t;
  | t::ts -> llproof_term o t; oprintf o ", "; llproof_term_list o ts;
;;

let rec llproof_prop o pr =
  let printf f = oprintf o f in
  match pr with
  | Efalse -> printf "false";
  | Etrue -> printf "true";
  | Enot (p, _) -> printf "~"; llproof_prop o p;
  | Eand (p1, p2, _) ->
      printf "(";
      llproof_prop o p1;
      printf " /\\ ";
      llproof_prop o p2;
      printf ")";
  | Eor (p1, p2, _) ->
      printf "(";
      llproof_prop o p1;
      printf " \\/ ";
      llproof_prop o p2;
      printf ")";
  | Eimply (p1, p2, _) ->
      printf "(";
      llproof_prop o p1;
      printf " => ";
      llproof_prop o p2;
      printf ")";
  | Eequiv (p1, p2, _) ->
      printf "(";
      llproof_prop o p1;
      printf " <=> ";
      llproof_prop o p2;
      printf ")";
  | Eall (v, t, p, _, _) ->
      printf "All %a, " print_vartype (v, t); llproof_prop o p;
  | Eex (v, t, p, _, _) ->
      printf "Ex %a, " print_vartype (v, t); llproof_prop o p;
  | Eapp ("=", [t1; t2], _) ->
      printf "(";
      llproof_term o t1;
      printf " = ";
      llproof_term o t2;
      printf ")";
  | Eapp (s, [], _) -> printf "%s" s;
  | Eapp (s, args, _) -> printf "%s(" s; llproof_term_list o args; printf ")";
  | Evar (s, _) -> printf "%s" s;
  | Emeta _ | Etau _ -> assert false;
;;

let binop_name = function
  | And -> "And"
  | Or -> "Or"
  | Imply -> "Imply"
  | Equiv -> "Equiv"
;;

let llproof_rule o r =
  let printf f = oprintf o f in
  match r with
  | Rfalse -> printf "---false";
  | Rnottrue -> printf "---nottrue";
  | Raxiom (p) -> printf "---axiom "; llproof_prop o p;
  | Rcut (p) -> printf "---cut "; llproof_prop o p;
  | Rnoteq (t) -> printf "---noteq "; llproof_term o t;
  | Rnotnot (p) -> printf "---notnot "; llproof_prop o p;
  | Rconnect (op, p, q) ->
      printf "---connect (%s, " (binop_name op);
      llproof_prop o p;
      printf ", ";
      llproof_prop o q;
      printf ")";
  | Rnotconnect (op, p, q) ->
      printf "---notconnect (%s, " (binop_name op);
      llproof_prop o p;
      printf ", ";
      llproof_prop o q;
      printf ")";
  | Rex (p, v) -> printf "---ex ("; llproof_prop o p; printf ", %s)" v;
  | Rall (p, t) ->
      printf "---all (";
      llproof_prop o p;
      printf ", ";
      llproof_term o t;
      printf ")";
  | Rnotex (p, t) ->
      printf "---notex (";
      llproof_prop o p;
      printf ", ";
      llproof_term o t;
      printf ")";
  | Rnotall (p, v) -> printf "---notall ("; llproof_prop o p; printf ", %s)" v;
  | Rpnotp (p, q) ->
      printf "---pnotp (";
      llproof_prop o p;
      printf ", ";
      llproof_prop o q;
      printf ")";
  | Rnotequal (t, u) ->
      printf "---notequal (";
      llproof_term o t;
      printf ", ";
      llproof_term o u;
      printf ")";
  | Rdefinition (folded, unfolded) ->
      printf "---definition";
  | Rextension (name, args, c, hyps) ->
      printf "---extension (%s" name;
      List.iter (fun x -> printf " "; llproof_prop o x) args;
      printf ")";
  | Rlemma (name, args) ->
      printf "---lemma %s [ " name;
      List.iter (fun x -> printf "%s " x) args;
      printf "]";
;;

let nodes = ref 0;;

let rec llproof_tree o i t =
  let printf = oprintf o in
  let prop_space p = llproof_prop o p; printf "   "; in
  indent o i; List.iter prop_space t.conc; printf "\n";
  indent o i; llproof_rule o t.rule; printf "\n";
  List.iter (llproof_tree o (i+1)) t.hyps;
  incr nodes;
;;

let print_idtype o (v, t) =
  if t = ""
  then oprintf o "%s " v
  else oprintf o "%s:\"%s\" " v t
;;

let llproof_lemma o {name=name; params=params; proof=tree} =
  let printf f = oprintf o f in
  printf "%s" name;
  if params <> [] then begin
    printf " [";
    List.iter (print_idtype o) params;
    printf "]";
  end;
  printf "\n";
  llproof_tree o 1 tree;
  printf "\n";
;;

let llproof o p =
  List.iter (llproof_lemma o) p;
  flush ();
;;
