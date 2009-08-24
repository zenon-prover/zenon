(*  Copyright 2008 INRIA  *)
Version.add "$Id: lltoisar.ml,v 1.30 2009-08-24 12:15:23 doligez Exp $";;

open Printf;;

open Expr;;
open Llproof;;
open Misc;;
open Namespace;;

module Dict = Set.Make (String);;

let rec dict_addlist l d =
  match l with
  | [] -> d
  | h::t -> dict_addlist t (Dict.add h d)
;;

let dict_add x d = Dict.add x d;;
let dict_mem x d = Dict.mem x d;;
let dict_empty = Dict.empty;;

module Int = struct
  type t = int;;
  let compare = Pervasives.compare;;
end;;
module Hypdict = Map.Make (Int);;

let iprintf i oc fmt (* args *) =
  fprintf oc "%s" (String.make i ' ');
  fprintf oc fmt (* args *);
;;

let iinc i = if i >= 15 then i else i+1;;

let vname e = "?z_h" ^ (base26 (Index.get_number e));;
let hname hyps e =
  let n = Index.get_number e in
  try Hypdict.find n hyps
  with Not_found -> "z_H" ^ (base26 n)
;;

let apply lam arg =
  match lam with
  | Elam (v, t, e1, _) -> substitute [(v, arg)] e1
  | _ -> assert false
;;

let rec p_list dict init printer sep oc l =
  match l with
  | [] -> ()
  | [x] -> fprintf oc "%s%a" init (printer dict) x;
  | h::t ->
      fprintf oc "%s%a%s" init (printer dict) h sep;
      p_list dict init printer sep oc t;
;;

let tr_infix s =
  match s with
  | "=" -> "="
  | "TLA.cup" -> "\\\\cup "
  | "TLA.cap" -> "\\\\cap "
  | "TLA.setminus" -> "\\\\ "
  | "TLA.in" -> "\\\\in "
  | "TLA.subseteq" -> "\\\\subseteq "
  | _ -> ""
;;

let is_infix s = tr_infix s <> "";;

let tr_constant s =
  match s with
  | "TLA.emptyset" -> "{}"
  | "TLA.infinity" -> "infinity"
  | _ -> s
;;

let tr_prefix s =
  if String.length s > 4 && String.sub s 0 4 = "TLA."
  then String.sub s 4 (String.length s - 4)
  else s
;;

let disjoint l1 l2 = not (List.exists (fun x -> List.mem x l1) l2);;

let rec p_expr env dict oc e =
  let poc fmt = fprintf oc fmt in
  match e with
  | _ when dict_mem (vname e) dict && disjoint env (get_fv e) ->
      poc "%s" (vname e)
  | Evar (v, _) when Mltoll.is_meta v ->
      poc "(CHOOSE x : TRUE)";
  | Evar (v, _) ->
      poc "%s" (tr_constant v);
  | Eapp ("TLA.set", l, _) ->
      poc "{%a}" (p_expr_list env dict) l;
  | Eapp ("TLA.tuple", l, _) ->
      poc "<<%a>>" (p_expr_list env dict) l;
  | Eapp ("TLA.CASE", l, _) ->
      poc "(CASE %a)" (p_case_arms env dict) l;
  | Eapp (f, [e1; e2], _) when is_infix f ->
      poc "(%a%s%a)" (p_expr env dict) e1 (tr_infix f) (p_expr env dict) e2;
  | Eapp (f, l, _) ->
      poc "%s(%a)" (tr_prefix f) (p_expr_list env dict) l;
  | Enot (Eapp ("=", [e1; e2], _), _) ->
      poc "(%a~=%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Enot (e1, _) ->
      poc "(~%a)" (p_expr env dict) e1;
  | Eand (e1, e2, _) ->
      poc "(%a&%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Eor (e1, e2, _) ->
      poc "(%a|%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Eimply (e1, e2, _) ->
      poc "(%a=>%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Eequiv (e1, e2, _) ->
      poc "(%a<=>%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Etrue ->
      poc "TRUE";
  | Efalse ->
      poc "FALSE";
  | Eall (Evar (x, _), _, e, _) ->
      poc "(\\\\A %s:%a)" x (p_expr (x::env) dict) e;
  | Eall _ -> assert false
  | Eex (Evar (x, _), _, e, _) ->
      poc "(\\\\E %s:%a)" x (p_expr (x::env) dict) e;
  | Eex _ -> assert false
  | Elam (Evar (x, _), _, e, _) ->
      poc "(\\<lambda>%s. %a)" x (p_expr (x::env) dict) e;
  | Elam _ -> assert false
  | Etau (Evar (x, _), _, e, _) ->
      poc "(CHOOSE %s:%a)" x (p_expr (x::env) dict) e;
  | Etau _ -> assert false
  | Emeta _ -> assert false


and p_expr_list env dict oc l = p_list dict "" (p_expr env) ", " oc l;

and p_case_arms env dict oc l =
  match l with
  | [] -> assert false
  | [e] -> fprintf oc "OTHER -> %a" (p_expr env dict) e
  | [c; e] ->
     fprintf oc "%a -> %a" (p_expr env dict) c (p_expr env dict) e;
  | c :: e :: t ->
     fprintf oc "%a -> %a [] " (p_expr env dict) c (p_expr env dict) e;
     p_case_arms env dict oc t;
;;

let p_expr dict oc e = p_expr [] dict oc e;;
let p_expr_list dict oc l = p_expr_list [] dict oc l;;

let p_apply dict oc (lam, arg) =
  let n_lam = vname lam in
  if dict_mem n_lam dict then
    fprintf oc "%s(%a)" n_lam (p_expr dict) arg
  else
    p_expr dict oc (apply lam arg)
;;

let mk_pat dict e =
  match e with
  | Evar (v, _) when not (Mltoll.is_meta v) -> ("_", dict)
  | _ ->
     let n = vname e in
     if dict_mem n dict then ("_", dict) else (n, dict_add n dict)
;;

let p_is dict oc h =
  let binary pre e1 op e2 post =
    let (p1, dict1) = mk_pat dict e1 in
    let (p2, dict2) = mk_pat dict1 e2 in
    if p1 = "_" && p2 = "_"
    then fprintf oc "\n"
    else fprintf oc " (is \"%s%s%s%s%s\")\n" pre p1 op p2 post;
    dict2
  in
  let unary pre e post =
    let (p, dict1) = mk_pat dict e in
    if p = "_"
    then fprintf oc "\n"
    else fprintf oc " (is \"%s%s%s\")\n" pre p post;
    dict1
  in
  match h with
  | Eand (e1, e2, _) -> binary "" e1 "&" e2 ""
  | Eor (e1, e2, _) -> binary "" e1 "|" e2 ""
  | Eimply (e1, e2, _) -> binary "" e1 "=>" e2 ""
  | Eequiv (e1, e2, _) -> binary "" e1 "<=>" e2 ""
  | Enot (Eand (e1, e2, _), _) -> binary "~(" e1 "&" e2 ")"
  | Enot (Eor (e1, e2, _), _) -> binary "~(" e1 "|" e2 ")"
  | Enot (Eimply (e1, e2, _), _) -> binary "~(" e1 "=>" e2 ")"
  | Enot (Eequiv (e1, e2, _), _) -> binary "~(" e1 "<=>" e2 ")"
  | Eall (v, t, e1, _) -> unary "\\\\A x : " (elam (v, t, e1)) "(x)"
  | Eex (v, t, e1, _) -> unary "\\\\E x : " (elam (v, t, e1)) "(x)"
  | Enot (Eall (v, t, e1, _), _) -> unary "~(\\\\A x : " (elam (v, t, e1)) "(x))"
  | Enot (Eex (v, t, e1, _), _) -> unary "~(\\\\E x : " (elam (v, t, e1)) "(x))"
  | Enot (Enot (e1, _), _) -> unary "~~" e1 ""
  | Eapp ("=", [e1; e2], _) -> binary "" e1 "=" e2 ""
  | Enot (Eapp ("=", [e1; e2], _), _) -> binary "" e1 "~=" e2 ""
  | Enot (e1, _) -> unary "~" e1 ""
  | _ -> unary "" h ""
;;

let p_assume hyps i dict oc h =
  iprintf i oc "assume %s:\"%a\"" (hname hyps h) (p_expr dict) h;
  p_is dict oc h
;;

let p_sequent hyps i dict oc hs =
  List.fold_left (fun dict h -> p_assume hyps i dict oc h) dict hs
;;

let rec p_tree hyps i dict oc proof =
  let alpha = p_alpha hyps i dict oc in
  let beta = p_beta hyps i dict oc in
  let gamma = p_gamma hyps i dict oc in
  let delta = p_delta hyps i dict oc in
  match proof.rule with
  | Rconnect (And, e1, e2) ->
     alpha "and" (eand (e1, e2)) [e1; e2] proof.hyps;
  | Rconnect (Or, e1, e2) ->
     beta "or" (eor (e1, e2)) [[e1]; [e2]] proof.hyps;
  | Rconnect (Imply, e1, e2) ->
     beta "imply" (eimply (e1, e2)) [[enot (e1)]; [e2]] proof.hyps;
  | Rconnect (Equiv, e1, e2) ->
     beta "equiv" (eequiv (e1, e2)) [[enot (e1); enot (e2)]; [e1; e2]]
          proof.hyps;
  | Rnotconnect (And, e1, e2) ->
     beta "notand" (enot (eand (e1, e2))) [[enot (e1)]; [enot (e2)]] proof.hyps;
  | Rnotconnect (Or, e1, e2) ->
     alpha "notor" (enot (eor (e1, e2))) [enot (e1); enot (e2)] proof.hyps;
  | Rnotconnect (Imply, e1, e2) ->
     alpha "notimply" (enot (eimply (e1, e2))) [e1; enot (e2)] proof.hyps;
  | Rnotconnect (Equiv, e1, e2) ->
     beta "notequiv" (enot (eequiv (e1, e2)))
          [[enot (e1); e2]; [e1; enot (e2)]] proof.hyps;
  | Rextension ("zenon_case", args, con, hs) ->
     Error.warn "proof involving CASE: will not be checked by Isabelle";
     iprintf i oc "show FALSE\n";
     iprintf i oc "ML_command {* set quick_and_dirty; *} sorry\n";
  | Rextension (name, args, con, []) ->
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (hname hyps e) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s [of %a, OF %a])\n" name
             (p_list dict "" p_arg " ") args (p_list dict "" p_con " ") con;
  | Rextension (name, args, con, [hs]) ->
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (hname hyps e) in
     let p_hyp (dict, j) h =
       iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
       let dict2 = p_is dict oc h in
       iprintf i oc "by (rule %s_%d [of %a, OF %a])\n" name j
               (p_list dict2 "" p_arg " ") args (p_list dict2 "" p_con " ") con;
       (dict2, j+1)
     in
     let (dict3, _) = List.fold_left p_hyp (dict, 0) hs in
     begin match proof.hyps with
     | [t] -> p_tree hyps i dict3 oc t;
     | _ -> assert false
     end;
  | Rextension (name, args, con, hs) ->
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (hname hyps e) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule %s [of %a, OF %a])\n" name
             (p_list dict "" p_arg " ") args (p_list dict "" p_con " ") con;
     let rec p_sub dict l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          let dict2 = p_sequent hyps (iinc i) dict oc h in
          p_tree hyps (iinc i) dict2 oc t;
          iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub dict hs ts;
       | [], [] -> ()
       | _, _ -> assert false
     in
     p_sub dict hs proof.hyps;
  | Rnotnot (e1) ->
     alpha "notnot" (enot (enot e1)) [e1] proof.hyps;
  | Rex (Eex (x, t, e1, _) as conc, e2) ->
     delta "ex_choose" false (elam (x, t, e1)) e2 conc proof.hyps;
  | Rex _ -> assert false
  | Rnotall (Eall (x, t, e1, _) as nconc, e2) ->
     delta "notall_choose" true (elam (x, t, e1)) e2 (enot nconc) proof.hyps;
  | Rnotall _ -> assert false
  | Rall (Eall (x, t, e1, _) as conc, e2) ->
     gamma "all" false (elam (x, t, e1)) e2 conc proof.hyps;
  | Rall _ -> assert false
  | Rnotex (Eex (x, t, e1, _) as nconc, e2) ->
     gamma "notex" true (elam (x, t, e1)) e2 (enot nconc) proof.hyps;
  | Rnotex _ -> assert false
  | Rlemma (l, a) ->
     let rec filter_vars l =
      match l with
      | [] -> []
      | Evar (v, _) :: t -> v :: filter_vars t
      | Etau _ :: t -> filter_vars t
      | _ -> assert false
     in
     let pr dict oc v = fprintf oc "?%s=%s" v v in
     let pr_hyp dict oc h = fprintf oc "%s" (hname hyps h) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s [where %a, OF %a])\n" l
             (p_list dict "" pr " and ") (filter_vars a)
             (p_list dict "" pr_hyp " ") proof.conc;
  | Rcut (e1) ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule zenon_em [of \"%a\"])\n" (p_expr dict) e1;
     let rec p_sub dict l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          let dict2 = p_sequent hyps (iinc i) dict oc h in
          p_tree hyps (iinc i) dict2 oc t;
          iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub dict hs ts;
       | [], [] -> ()
       | _ -> assert false
     in p_sub dict [[e1]; [enot e1]] proof.hyps;
  | Raxiom (e1) ->
     let n_e1 = hname hyps e1 in
     let n_ne1 = hname hyps (enot e1) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule notE [OF %s %s])\n" n_ne1 n_e1;
  | Rdefinition (name, s, conc, hyp) ->
     let n_conc = hname hyps conc in
     let n_hyp = hname hyps hyp in
     iprintf i oc "have %s_%s: \"%a == %a\"" n_hyp n_conc
             (p_expr dict) hyp (p_expr dict) conc;
     let (p_h, dict1) = mk_pat dict hyp in
     let (p_c, dict2) = mk_pat dict1 conc in
     fprintf oc " (is \"%s == %s\")\n" p_h p_c;
     iprintf i oc "by (unfold %s)\n" name;
     iprintf i oc "have %s: \"%a\"" n_hyp (p_expr dict2) hyp;
     let dict3 = p_is dict2 oc hyp in
     iprintf i oc "by (unfold %s_%s, fact %s)\n" n_hyp n_conc n_conc;
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     p_tree hyps i dict3 oc t;
  | Rnotequal (Eapp (f, args1, _) as e1, (Eapp (g, args2, _) as e2)) ->
     assert (f = g);
     let e = enot (eapp ("=", [e1; e2])) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule zenon_noteq [of \"%a\"])\n" (p_expr dict) e2;
     let pr d x y z = p_sub_equal hyps (iinc i) d oc x y z in
     let dict2 = list_fold_left3 pr dict args1 args2 proof.hyps in
     let mk l = enot (eapp ("=", [eapp (f, l); e2])) in
     p_subst hyps i dict2 oc mk args1 args2 [] e;
  | Rnotequal _ -> assert false
  | Rpnotp (Eapp (p, args1, _) as pp, (Enot (Eapp (q, args2, _), _) as np)) ->
     assert (p = q);
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule notE [OF %s])\n" (hname hyps np);
     let pr d x y z = p_sub_equal hyps (iinc i) d oc x y z in
     let dict2 = list_fold_left3 pr dict args1 args2 proof.hyps in
     let mk l = eapp (p, l) in
     p_subst hyps i dict2 oc mk args1 args2 [] pp;
  | Rpnotp _ -> assert false
  | Rnoteq e1 ->
     let neq = enot (eapp ("=", [e1; e1])) in
     let n_neq = hname hyps neq in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_noteq [OF %s])\n" n_neq;
  | Reqsym (e1, e2) ->
     let eq = eapp ("=", [e1; e2]) in
     let n_eq = hname hyps eq in
     let neq = enot (eapp ("=", [e2; e1])) in
     let n_neq = hname hyps neq in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_eqsym [OF %s %s])\n" n_eq n_neq;
  | Rnottrue ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_nottrue [OF %s])\n" (hname hyps (enot etrue))
  | Rfalse ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s)\n" (hname hyps efalse);
  | RcongruenceLR (p, a, b) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let h0 = eapp ("=", [a; b]) in
     let h1 = apply p a in
     let c = apply p b in
     iprintf i oc "have %s: \"%a\"" (hname hyps c) (p_expr dict) c;
     let dict2 = p_is dict oc c in
     iprintf i oc "by (rule subst [of \"%a\" \"%a\" \"%a\", OF %s %s])\n"
             (p_expr dict2) a (p_expr dict2) b (p_expr dict2) p
             (hname hyps h0) (hname hyps h1);
     p_tree hyps i dict2 oc t;
  | RcongruenceRL (p, a, b) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let h0 = eapp ("=", [b; a]) in
     let h1 = apply p a in
     let c = apply p b in
     iprintf i oc "have %s: \"%a\"" (hname hyps c) (p_expr dict) c;
     let dict2 = p_is dict oc c in
     iprintf i oc "by (rule ssubst [of \"%a\" \"%a\" \"%a\", OF %s %s])\n"
             (p_expr dict2) b (p_expr dict2) a (p_expr dict2) p
             (hname hyps h0) (hname hyps h1);
     p_tree hyps i dict2 oc t;

and p_alpha hyps i dict oc lem h0 hs sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let n_h0 = hname hyps h0 in
  let pr_h (dict, j) h =
    iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
    let dict2 = p_is dict oc h in
    iprintf i oc "by (rule zenon_%s_%d [OF %s])\n" lem j n_h0;
    (dict2, j+1)
  in
  let (dict3, _) = List.fold_left pr_h (dict, 0) hs in
  p_tree hyps i dict3 oc t;

and p_beta hyps i dict oc lem h0 hs sub =
  let n0 = hname hyps h0 in
  iprintf i oc "show FALSE\n";
  iprintf i oc "proof (rule zenon_%s [OF %s])\n" lem n0;
  let rec p_sub dict l1 l2 =
    match l1, l2 with
    | h::hs, t::ts ->
       let dict2 = p_sequent hyps (iinc i) dict oc h in
       p_tree hyps (iinc i) dict2 oc t;
       iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
       p_sub dict hs ts;
    | [], [] -> ()
    | _ -> assert false
  in
  p_sub dict hs sub;

and p_gamma hyps i dict oc lem neg lam e conc sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, negs) = if neg then (enot, "~") else ((fun x -> x), "") in
  let body = ng (apply lam e) in
  let n_body = hname hyps body in
  iprintf i oc "have %s: \"%s%a\"" n_body negs (p_apply dict) (lam, e);
  let dict2 = p_is dict oc body in
  iprintf i oc "by (rule zenon_%s_0 [of \"%a\" \"%a\", OF %s])\n"
          lem (p_expr dict2) lam (p_expr dict2) e (hname hyps conc);
  p_tree hyps i dict2 oc t;

and p_delta hyps i dict oc lem neg lam e conc sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, negs) = if neg then (enot, "~") else ((fun x -> x), "") in
  let body = ng (apply lam e) in
  let n_body = hname hyps body in
  iprintf i oc "have %s: \"%s%a\"" n_body negs (p_apply dict) (lam, e);
  let dict2 = p_is dict oc body in
  iprintf i oc "by (rule zenon_%s_0 [of \"%a\", OF %s])\n"
          lem (p_expr dict2) lam (hname hyps conc);
  p_tree hyps i dict2 oc t;

and p_sub_equal hyps i dict oc e1 e2 prf =
  let eq = eapp ("=", [e1; e2]) in
  if Expr.equal e1 e2 || List.exists (Expr.equal eq) prf.conc
  then dict
  else begin
    let n_eq = enot (eq) in
    iprintf i oc "have %s: \"%a\"" (hname hyps eq) (p_expr dict) eq;
    let dict2 = p_is dict oc eq in
    let rev_eq = eapp ("=", [e2; e1]) in
    if List.exists (Expr.equal rev_eq) prf.conc then begin
      iprintf i oc "by (rule sym [OF %s])\n" (hname hyps rev_eq);
    end else begin
      iprintf i oc "proof (rule zenon_nnpp [of \"%a\"])\n" (p_expr dict2) eq;
      let dict3 = p_sequent hyps (iinc i) dict2 oc [n_eq] in
      p_tree hyps (iinc i) dict3 oc prf;
      iprintf i oc "qed\n";
    end;
    dict2
  end

and p_subst hyps i dict oc mk l1 l2 rl2 prev =
  match l1, l2 with
  | [], [] ->
     iprintf (iinc i) oc "thus \"%a\" .\n" (p_expr dict) prev;
     iprintf i oc "qed\n";
  | h1 :: t1, h2 :: t2 ->
     let newrl2 = h2 :: rl2 in
     if Expr.equal h1 h2 then
       p_subst hyps i dict oc mk t1 t2 newrl2 prev
     else begin
       let args = List.rev_append newrl2 t1 in
       let e = mk args in
       let n_e = hname hyps e in
       iprintf (iinc i) oc "have %s: \"%a\"" n_e (p_expr dict) e;
       let dict2 = p_is dict oc e in
       let eq = eapp ("=", [h1; h2]) in
       iprintf (iinc i) oc "by (rule subst [OF %s], fact %s)\n" (hname hyps eq)
               (hname hyps prev);
       p_subst hyps i dict2 oc mk t1 t2 newrl2 e;
     end;
  | _, _ -> assert false
;;

let p_lemma hyps i dict oc lem =
  iprintf i oc "have %s: \"" lem.name;
  let f (ty, e) accu =
    match e with
    | Evar (x, _) -> x :: accu
    | Etau _ -> accu
    | _ -> assert false
  in
  let params = List.fold_right f lem.params [] in
  List.iter (fprintf oc "!!%s. ") params;
  List.iter (fun x -> fprintf oc "%a ==> " (p_expr dict) x) lem.proof.conc;
  fprintf oc "FALSE\"";

  let f (pats, dict) e = let (p, dict1) = mk_pat dict e in (p :: pats, dict1) in
  let (pats, dict1) = List.fold_left f ([], dict) lem.proof.conc in
  if List.for_all ((=) "_") pats then begin
    fprintf oc "\n";
  end else begin
    fprintf oc " (is \"";
    List.iter (fprintf oc "%s ==> ") (List.rev pats);
    fprintf oc "FALSE\")\n";
  end;
  iprintf i oc "proof -\n";
  List.iter (iprintf (iinc i) oc "fix \"%s\"\n") params;
  let p_asm dict x =
    iprintf (iinc i) oc "assume %s:\"%a\"" (hname hyps x) (p_expr dict) x;
    p_is dict oc x
  in
  let dict2 = List.fold_left p_asm dict1 lem.proof.conc in
  p_tree hyps (iinc i) dict2 oc lem.proof;
  iprintf i oc "qed\n";
;;

let rec get_ngoal phrases =
  match phrases with
  | [] -> enot (efalse)
  | Phrase.Hyp (n, e, _) :: t when n = goal_name -> e
  | _ :: t -> get_ngoal t
;;

module HE = Hashtbl.Make (Expr);;

let mk_hyp_dict phrases =
  let f hyps p =
    match p with
    | Phrase.Hyp ("", _, _) -> hyps
    | Phrase.Hyp (name, e, _) -> Hypdict.add (Index.get_number e) name hyps;
    | _ -> hyps
  in
  List.fold_left f Hypdict.empty phrases
;;

let p_theorem oc thm phrases lemmas =
  let ngoal = get_ngoal phrases in
  let goal =
    match ngoal with
    | Enot (e1, _) -> e1
    | _ -> assert false
  in
  let hyps = List.filter (fun x -> x <> ngoal) thm.proof.conc in
  let hypnames = mk_hyp_dict phrases in
  iprintf 0 oc "proof (rule zenon_nnpp)\n";
  let i = iinc 0 in
  let p_asm dict x =
    if Hypdict.mem (Index.get_number x) hypnames then dict else begin
      iprintf i oc "have %s:\"%a\"" (hname hypnames x) (p_expr dict) x;
      let dict2 = p_is dict oc x in
      iprintf i oc "by fact\n";
      dict2
    end
  in
  let dict3 = List.fold_left p_asm dict_empty hyps in
  List.iter (p_lemma hypnames i dict3 oc) lemmas;
  let dict4 = p_sequent hypnames i dict3 oc [enot (goal)] in
  p_tree hypnames i dict4 oc thm.proof;
  iprintf 0 oc "qed\n";
;;

let rec p_lemmas oc llp phrases lemmas =
  match llp with
  | [] -> assert false
  | [x] -> p_theorem oc x phrases (List.rev lemmas);
  | h::t -> p_lemmas oc t phrases (h::lemmas);
;;

let output oc phrases ppphrases llp =
  if !Globals.ctx_flag then begin
    fprintf oc "(* BEGIN-CONTEXT *)\n";
    fprintf oc "theory zenon_tmp_theory imports Constant Zenon begin\n";
    let f p =
      match p with
      | Phrase.Hyp ("", _, _) -> ()
      | Phrase.Hyp (name, e, _) when name <> Namespace.goal_name ->
         fprintf oc "axioms %s: \"%a\"\n" name (p_expr dict_empty) e
      | Phrase.Hyp _ -> ()
      | Phrase.Def (DefReal (name, sym, args, body)) ->
         let isym = tr_prefix sym in
         fprintf oc "consts \"%s\" :: \"[%a] \\<Rightarrow> c\"\n" isym
                 (p_list dict_empty "c" (fun _ _ _ -> ()) ",") args;
         fprintf oc "defs \"%s\": \"%s(%a) \\<equiv> %a\"\n" name isym
                 (p_list dict_empty "" p_expr ",") args
                 (p_expr dict_empty) body;
      | Phrase.Def _ -> assert false
      | Phrase.Sig _ -> failwith "signatures not implemented in isar output"
      | Phrase.Inductive _ ->
         failwith "inductives not implemented in isar output"
    in
    List.iter f phrases;
    fprintf oc "theorem zenon_tmp_thm:\n";
    let f p =
      match p with
      | Phrase.Hyp ("", e, _) ->
         fprintf oc "assumes \"%a\"\n" (p_expr dict_empty) e;
      | _ -> ()
    in
    List.iter f phrases;
    let f p =
      match p with
      | Phrase.Hyp (name, Enot (e, _), _) when name = Namespace.goal_name ->
         fprintf oc "shows \"%a\"\n" (p_expr dict_empty) e;
      | _ -> ()
    in
    List.iter f phrases;
    fprintf oc "(* END-CONTEXT *)\n";
  end;
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
  p_lemmas oc llp phrases [];
  if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
  !Coqterm.constants_used
;;
