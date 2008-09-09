(*  Copyright 2008 INRIA  *)
Version.add "$Id: lltoisar.ml,v 1.6 2008-09-09 15:09:16 doligez Exp $";;

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

let iprintf i oc fmt (* args *) =
  fprintf oc "%s" (String.make i ' ');
  fprintf oc fmt (* args *);
;;

let iinc i = if i >= 20 then i else i+2;;

let base36 x =
  if x = 0 then "0" else begin
    assert (x > 0);
    let digit x =
      if x < 10 then Char.chr (Char.code '0' + x)
      else if x < 36 then Char.chr (Char.code 'a' + x - 10)
      else assert false
    in
    let rec conv x =
      if x = 0 then "" else sprintf "%s%c" (conv (x/36)) (digit (x mod 36))
    in
    conv x
  end
;;

let getname e = "z_H" ^ (base36 (Index.get_number e));;

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
  | "TLA.cup" -> "\\\\cup"
  | "TLA.cap" -> "\\\\cap"
  | "TLA.setminus" -> "\\\\"
  | "TLA.in" -> "\\\\in"
  | "TLA.subseteq" -> "\\\\subseteq"
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

let rec p_expr dict oc e =
  let poc fmt = fprintf oc fmt in
  if dict_mem (getname e) dict then
    poc "?%s" (getname e)
  else match e with
  | Evar (v, _) when Mltoll.is_meta v ->
      poc "(CHOOSE x : TRUE)";
  | Evar (v, _) ->
      poc "%s" (tr_constant v);
  | Eapp (f, [e1; e2], _) when is_infix f ->
      poc "(%a %s %a)" (p_expr dict) e1 (tr_infix f) (p_expr dict) e2;
  | Eapp (f, l, _) ->
      poc "%s(%a)" (tr_prefix f) (p_expr_list dict) l;
  | Enot (e, _) ->
      poc "(~%a)" (p_expr dict) e;
  | Eand (e1, e2, _) ->
      poc "(%a&%a)" (p_expr dict) e1 (p_expr dict) e2;
  | Eor (e1, e2, _) ->
      poc "(%a|%a)" (p_expr dict) e1 (p_expr dict) e2;
  | Eimply (e1, e2, _) ->
      poc "(%a=>%a)" (p_expr dict) e1 (p_expr dict) e2;
  | Eequiv (e1, e2, _) ->
      poc "(%a<=>%a)" (p_expr dict) e1 (p_expr dict) e2;
  | Etrue ->
      poc "TRUE";
  | Efalse ->
      poc "FALSE";
  | Eall (Evar (x, _), _, e, _) ->
      poc "(\\\\A %s : %a)" x (p_expr dict) e;
  | Eall _ -> assert false
  | Eex (Evar (x, _), _, e, _) ->
      poc "(\\\\E %s : %a)" x (p_expr dict) e;
  | Eex _ -> assert false
  | Elam (Evar (x, _), _, e, _) ->
      poc "(\\<lambda>%s. %a)" x (p_expr dict) e;
  | Elam _ -> assert false
  | Etau (Evar (x, _), _, e, _) ->
      poc "(CHOOSE %s : %a)" x (p_expr dict) e;
  | Etau _ -> assert false
  | Emeta _ -> assert false


and p_expr_list dict oc l = p_list dict "" p_expr ", " oc l;
;;

let p_apply dict oc (lam, arg) =
  let n_lam = getname lam in
  if dict_mem n_lam dict then
    fprintf oc "?%s(%a)" n_lam (p_expr dict) arg
  else
    p_expr dict oc (apply lam arg)
;;

let mk_pat dict n = if dict_mem n dict then "_" else ("?"^n);;

let p_is dict oc h =
  let binary pre e1 op e2 post =
    let n1 = getname e1 in
    let n2 = getname e2 in
    if dict_mem n1 dict && dict_mem n2 dict then begin
      fprintf oc "\n";
      dict
    end else begin
      fprintf oc " (is \"%s%s%s%s%s\")\n"
              pre (mk_pat dict n1) op (mk_pat dict n2) post;
      dict_addlist [n1; n2] dict
    end
  in
  let unary pre e post =
    let n = getname e in
    if dict_mem n dict then begin
      fprintf oc "\n";
      dict
    end else begin
      fprintf oc " (is \"%s%s%s\")\n" pre (mk_pat dict n) post;
      dict_add n dict
    end
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

let p_assume i dict oc h =
  iprintf i oc "assume %s:\"%a\"" (getname h) (p_expr dict) h;
  p_is dict oc h
;;

let p_sequent i dict oc hs =
  let dict2 = List.fold_left (fun dict h -> p_assume i dict oc h) dict hs in
  dict2
;;

let rec p_tree i dict oc proof =
  let alpha = p_alpha i dict oc in
  let beta = p_beta i dict oc in
  let gamma = p_gamma i dict oc in
  let delta = p_delta i dict oc in
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
  | Rextension (name, args, con, [hs]) ->
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (getname e) in
     let p_hyp (dict, j) h =
       iprintf i oc "have %s: \"%a\"" (getname h) (p_expr dict) h;
       let dict2 = p_is dict oc h in
       iprintf i oc "by (rule %s_%d [of %a], fact %a)\n" name j
               (p_list dict2 "" p_arg " ") args (p_list dict2 "" p_con " ") con;
       (dict2, j+1)
     in
     let (dict3, _) = List.fold_left p_hyp (dict, 0) hs in
     begin match proof.hyps with
     | [t] -> p_tree i dict3 oc t;
     | _ -> assert false
     end;
  | Rextension (name, args, con, hs) ->
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (getname e) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule %s [of %a], fact %a)\n" name
             (p_list dict "" p_arg " ") args (p_list dict "" p_con " ") con;
     let rec p_sub dict l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          let dict2 = p_sequent (iinc i) dict oc h in
          p_tree (iinc i) dict2 oc t;
          iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub dict hs ts;
       | [], [] -> ()
       | _, _ -> assert false
     in
     p_sub dict hs proof.hyps;
  | Rnotnot (e1) ->
     alpha "notnot" (enot (enot e1)) [e1] proof.hyps;
  | Rex (Eex (x, t, e1, _) as p, v) ->
     delta "ex" p v false (elam (x, t, e1)) proof.hyps;
  | Rex _ -> assert false
  | Rnotall (Eall (x, t, e1, _) as p, v) ->
     delta "notall" p v true (elam (x, t, e1)) proof.hyps;
  | Rnotall _ -> assert false
  | Rall (Eall (x, t, e1, _) as conc, e2) ->
     gamma "all" false (elam (x, t, e1)) e2 conc proof.hyps;
  | Rall _ -> assert false
  | Rnotex (Eex (x, t, e1, _) as nconc, e2) ->
     gamma "notex" true (elam (x, t, e1)) e2 (enot nconc) proof.hyps;
  | Rnotex _ -> assert false
  | Rlemma (l, a) ->
     let pr dict oc x = fprintf oc "%s" x in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s [of %a])\n" l (p_list dict "" pr " ") a;
  | Rcut (e1) ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule zenon_em [of \"%a\"])\n" (p_expr dict) e1;
     let rec p_sub dict l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          let dict2 = p_sequent (iinc i) dict oc h in
          p_tree (iinc i) dict2 oc t;
          iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub dict hs ts;
       | [], [] -> ()
       | _ -> assert false
     in p_sub dict [[e1]; [e1]] proof.hyps;
  | Raxiom (e1) ->
     let n_e1 = getname e1 in
     let n_ne1 = getname (enot e1) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule notE [OF %s %s])\n" n_ne1 n_e1;
  | Rdefinition (name, s, conc, hyp) ->
     let n_conc = getname conc in
     let n_hyp = getname hyp in
     let n_h = getname hyp in
     let n_c = getname conc in
     iprintf i oc "have %s_%s: \"%a == %a\"" n_hyp n_conc
             (p_expr dict) hyp (p_expr dict) conc;
     fprintf oc " (is \"%s == %s\")\n" (mk_pat dict n_h) (mk_pat dict n_c);
     let dict2 = dict_addlist [n_h; n_c] dict in
     iprintf i oc "by (unfold %s)\n" name;
     iprintf i oc "have %s: \"%a\"" n_hyp (p_expr dict2) hyp;
     let dict3 = p_is dict2 oc hyp in
     iprintf i oc "by (unfold %s_%s, fact %s)\n" n_hyp n_conc (getname conc);
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     p_tree i dict3 oc t;
  | Rnotequal _ -> assert false (* TODO *)
  | Rpnotp (Eapp (p, args1, _) as pp, (Enot (Eapp (q, args2, _), _) as np)) ->
     assert (p = q);
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule notE [OF %s])\n" (getname np);
     let pr d x y z = p_sub_equal (iinc i) d oc x y z in
     let dict2 = list_fold_left3 pr dict args1 args2 proof.hyps in
     let mk l = eapp (p, l) in
     p_subst (iinc i) dict2 oc mk args1 args2 [] (getname pp);
  | Rpnotp _ -> assert false
  | Rnoteq e1 ->
     let neq = enot (eapp ("=", [e1; e1])) in
     let n_neq = getname neq in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_noteq [OF %s])\n" n_neq;
  | Rnottrue ->
     let nh = getname (enot etrue) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_nottrue [OF %s])\n" nh;
  | Rfalse ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s)\n" (getname efalse);

and p_alpha i dict oc lem h0 hs sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let n_h0 = getname h0 in
  let pr_h (dict, j) h =
    iprintf i oc "have %s: \"%a\"" (getname h) (p_expr dict) h;
    let dict2 = p_is dict oc h in
    iprintf i oc "by (rule zenon_%s_%d [OF %s])\n" lem j n_h0;
    (dict2, j+1)
  in
  let (dict3, _) = List.fold_left pr_h (dict, 0) hs in
  p_tree i dict3 oc t;

and p_beta i dict oc lem h0 hs sub =
  let n0 = getname h0 in
  iprintf i oc "show FALSE\n";
  iprintf i oc "proof (rule zenon_%s [OF %s])\n" lem n0;
  let rec p_sub dict l1 l2 =
    match l1, l2 with
    | h::hs, t::ts ->
       let dict2 = p_sequent (iinc i) dict oc h in
       p_tree (iinc i) dict2 oc t;
       iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
       p_sub dict hs ts;
    | [], [] -> ()
    | _ -> assert false
  in
  p_sub dict hs sub;

and p_gamma i dict oc lem neg lam e conc sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, negs) = if neg then (enot, "~") else ((fun x -> x), "") in
  let body = ng (apply lam e) in
  let n_body = getname body in
  iprintf i oc "have %s: \"%s%a\"" n_body negs (p_apply dict) (lam, e);
  let dict2 = p_is dict oc body in
  iprintf i oc "by (rule zenon_%s_0 [of \"%a\" \"%a\"], fact %s)\n"
          lem (p_expr dict2) lam (p_expr dict2) e (getname conc);
  p_tree i dict2 oc t;

and p_delta i dict oc lem h0 v neg lam sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, negs) = if neg then (enot, "~") else ((fun x -> x), "") in
  let h00 = ng h0 in
  let n00 = getname h00 in
  iprintf i oc "show FALSE\n";
  iprintf i oc "proof (rule zenon_%s [OF %s])\n" lem n00;
  iprintf (iinc i) oc "fix %s\n" v;
  let h =
    match lam with
    | Elam (x, _, e1, _) -> ng (substitute [(x, evar (v))] e1)
    | _ -> assert false
  in
  let n_h = getname h in
  iprintf (iinc i) oc "assume %s: \"%s%a\"" n_h negs (p_apply dict) (lam, evar (v));
  let dict2 = p_is dict oc h in
  p_tree (iinc i) dict2 oc t;
  iprintf i oc "qed\n";

and p_sub_equal i dict oc e1 e2 prf =
  let eq = eapp ("=", [e1; e2]) in
  if Expr.equal e1 e2 || List.exists (Expr.equal eq) prf.conc
  then dict
  else begin
    let n_eq = enot (eq) in
    iprintf i oc "have %s: \"%a\"" (getname eq) (p_expr dict) eq;
    let dict2 = p_is dict oc eq in
    let rev_eq = eapp ("=", [e2; e1]) in
    if List.exists (Expr.equal rev_eq) prf.conc then begin
      iprintf i oc "by (rule sym [OF %s])\n" (getname rev_eq);
    end else begin
      iprintf i oc "proof (rule zenon_nnpp [of \"%a\"])\n" (p_expr dict2) eq;
      let dict3 = p_sequent (iinc i) dict2 oc [n_eq] in
      p_tree (iinc i) dict3 oc prf;
      iprintf i oc "qed\n";
    end;
    dict2
  end

and p_subst i dict oc mk l1 l2 rl2 prev =
  match l1, l2 with
  | [], [] ->
     iprintf i oc "thus \"?%s\" .\nqed\n" prev;
  | h1 :: t1, h2 :: t2 ->
     let newrl2 = h2 :: rl2 in
     if Expr.equal h1 h2 then
       p_subst i dict oc mk t1 t2 newrl2 prev
     else begin
       let args = List.rev_append newrl2 t1 in
       let e = mk args in
       let n_e = getname e in
       iprintf i oc "have %s: \"%a\"" n_e (p_expr dict) e;
       let dict2 = p_is dict oc e in
       let eq = eapp ("=", [h1; h2]) in
       iprintf i oc "by (rule subst [OF %s], fact %s)\n" (getname eq) prev;
       p_subst i dict2 oc mk t1 t2 newrl2 n_e;
     end;
  | _, _ -> assert false
;;

let p_lemma i dict oc lem =
  iprintf i oc "have %s: \"" lem.name;
  List.iter (fun (x, y) -> fprintf oc "!!%s." x) lem.params;
  List.iter (fun x -> fprintf oc " %a ==>" (p_expr dict) x) lem.proof.conc;
  fprintf oc " FALSE\"\n";
  iprintf i oc "proof -\n";
  List.iter (fun (x, y) -> iprintf (iinc i) oc "fix \"%s\"\n" x) lem.params;
  let p_asm dict x =
    iprintf (iinc i) oc "assumes %s:\"%a\"" (getname x) (p_expr dict) x;
    p_is dict oc x
  in
  let dict2 = List.fold_left p_asm dict lem.proof.conc in
  p_tree (iinc i) dict2 oc lem.proof;
  iprintf i oc "qed\n";
;;

let rec get_goal phrases =
  match phrases with
  | [] -> efalse
  | Phrase.Hyp (n, e, _) :: t when n = goal_name -> e
  | _ :: t -> get_goal t
;;

module HE = Hashtbl.Make (Expr);;

let mk_hyp_table phrases =
  let tbl = HE.create 7 in
  let f p =
    match p with
    | Phrase.Hyp (name, e, _) -> HE.add tbl e name;
    | _ -> ()
  in
  List.iter f phrases;
  tbl
;;

let p_theorem oc thm phrases lemmas =
  let ngoal = get_goal phrases in
  let goal =
    match ngoal with
    | Enot (e1, _) -> e1
    | _ -> assert false
  in
  let hyps = List.filter (fun x -> x <> ngoal) thm.proof.conc in
  let hypnames = mk_hyp_table phrases in
  iprintf 0 oc "proof (rule zenon_nnpp)\n";
  let i = iinc 0 in
  let p_asm dict x =
    iprintf i oc "have %s:\"%a\"" (getname x) (p_expr dict) x;
    let dict2 = p_is dict oc x in
    begin match HE.find hypnames x with
    | "" -> iprintf i oc "by fact\n"
    | n -> iprintf i oc "by blast\n"
    end;
    dict2
  in
  let dict3 = List.fold_left p_asm dict_empty hyps in
  List.iter (p_lemma i dict_empty oc) lemmas;
  let dict4 = p_sequent i dict3 oc [enot (goal)] in
  p_tree i dict4 oc thm.proof;
  iprintf 0 oc "qed\n";
;;

let rec p_lemmas oc llp phrases lemmas =
  match llp with
  | [] -> assert false
  | [x] -> p_theorem oc x phrases (List.rev lemmas);
  | h::t -> p_lemmas oc t phrases (h::lemmas);
;;

let output oc phrases llp =
  if !Globals.ctx_flag then failwith "cannot output context in isar mode";
                                                                  (* TODO *)
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
  p_lemmas oc llp phrases [];
  if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
  !Coqterm.constants_used
;;
