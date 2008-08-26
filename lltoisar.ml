(*  Copyright 2008 INRIA  *)
Version.add "$Id: lltoisar.ml,v 1.2 2008-08-26 13:47:41 doligez Exp $";;

open Printf;;

open Expr;;
open Llproof;;
open Misc;;
open Namespace;;

let getname e = sprintf "%s%x" hyp_prefix (Index.get_number e);;

let tauname e = sprintf "%s%d" tau_prefix (Index.get_number e);;

let rec p_list init printer sep oc l =
  match l with
  | [] -> ()
  | [x] -> fprintf oc "%s%a" init printer x;
  | h::t ->
      fprintf oc "%s%a%s" init printer h sep;
      p_list init printer sep oc t;
;;

let tr_infix s =
  match s with
  | "=" -> "="
  | "TLA.in" -> "\\\\in"
  | "TLA.subseteq" -> "\\\\subseteq"
  | _ -> ""
;;

let is_infix s = tr_infix s <> "";;

let rec p_expr oc e =
  let poc fmt = fprintf oc fmt in
  match e with
  | Evar (v, _) when Mltoll.is_meta v ->
      poc "(CHOOSE x : TRUE)";
  | Evar (v, _) ->
      poc "%s" v;
  | Eapp ("TLA.ALL", [s; Elam (Evar (v, _), t, p, _)], _) ->
      poc "(ALL %s in %a : %a)" v p_expr s p_expr p;
  | Eapp (f, [e1; e2], _) when is_infix f ->
      poc "(%a %s %a)" p_expr e1 (tr_infix f) p_expr e2;
  | Eapp (f, l, _) ->
      poc "%s(%a)" f p_expr_list l;
  | Enot (e, _) ->
      poc "(~%a)" p_expr e;
  | Eand (e1, e2, _) ->
      poc "(%a&%a)" p_expr e1 p_expr e2;
  | Eor (e1, e2, _) ->
      poc "(%a|%a)" p_expr e1 p_expr e2;
  | Eimply (e1, e2, _) ->
      poc "(%a=>%a)" p_expr e1 p_expr e2;
  | Eequiv (e1, e2, _) ->
      poc "(%a<=>%a)" p_expr e1 p_expr e2;
  | Etrue ->
      poc "TRUE";
  | Efalse ->
      poc "FALSE";
  | Eall (Evar (x, _), _, e, _) ->
      poc "(\\\\A %s : %a)" x p_expr e;
  | Eall _ -> assert false
  | Eex (Evar (x, _), _, e, _) ->
      poc "(\\\\E %s : %a)" x p_expr e;
  | Eex _ -> assert false
  | Elam (Evar (x, _), _, e, _) ->
      poc "(\\<lambda>%s. %a)" x p_expr e;
  | Elam _ -> assert false
  | Etau (Evar (x, _), _, e, _) ->
      poc "(CHOOSE %s : %a)" x p_expr e;
  | Etau _ -> assert false
  | Emeta _ -> assert false


and p_expr_list oc l = p_list "" p_expr ", " oc l;
;;

let make_pattern h =
  match h with
  | Eand (e1, e2, _) ->
     Some (sprintf "\"?%s&?%s\"" (getname e1) (getname e2));
  | Eor (e1, e2, _) ->
     Some (sprintf "\"?%s|?%s\"" (getname e1) (getname e2));
  | Eimply (e1, e2, _) ->
     Some (sprintf "\"?%s=>?%s\"" (getname e1) (getname e2));
  | Eequiv (e1, e2, _) ->
     Some (sprintf "\"?%s<=>?%s\"" (getname e1) (getname e2));
  | Enot (Eand (e1, e2, _), _) ->
     Some (sprintf "\"~(?%s&?%s)\"" (getname e1) (getname e2));
  | Enot (Eor (e1, e2, _), _) ->
     Some (sprintf "\"~(?%s|?%s)\"" (getname e1) (getname e2));
  | Enot (Eimply (e1, e2, _), _) ->
     Some (sprintf "\"~(?%s=>?%s)\"" (getname e1) (getname e2));
  | Enot (Eequiv (e1, e2, _), _) ->
     Some (sprintf "\"~(?%s<=>?%s)\"" (getname e1) (getname e2));
  | Eall (v, t, e1, _) ->
     Some (sprintf "\"\\\\A x : ?%s x\"" (getname (elam (v, t, e1))));
  | Eex (v, t, e1, _) ->
     Some (sprintf "\"\\\\E x : ?%s x\"" (getname (elam (v, t, e1))));
  | Enot (Eall (v, t, e1, _), _) ->
     Some (sprintf "\"~(\\\\A x : ?%s x)\"" (getname (elam (v, t, e1))));
  | Enot (Eex (v, t, e1, _), _) ->
     Some (sprintf "\"~(\\\\E x : ?%s x)\"" (getname (elam (v, t, e1))));
  | Enot (Enot (e1, _), _) ->
     Some (sprintf "\"~~?%s\"" (getname e1));
  | Eapp ("=", [e1; e2], _) ->
     Some (sprintf "\"?%s = ?%s\"" (getname e1) (getname e2));
  | Enot (Eapp ("=", [e1; e2], _), _) ->
     Some (sprintf "\"?%s ~= ?%s\"" (getname e1) (getname e2));
  | _ ->
     None
;;

let p_is force oc h =
  match make_pattern h with
  | Some p -> fprintf oc "(is %s)\n" p;
  | None ->
      if force
      then fprintf oc "(is \"?%s\")\n" (getname h)
      else fprintf oc "\n";
;;

type signed =
  | P of expr
  | N of expr
;;

let sign e =
  match e with
  | Enot (e1, _) -> N e1
  | _ -> P e
;;

let p_assume oc h =
  let (hh, pre, ref) =
    match h with
    | P e -> (e, "", e)
    | N e -> (enot e, "~", e)
  in
  fprintf oc "assume %s:\"%s?%s\"" (getname hh) pre (getname ref);
  p_is false oc hh;
;;

let p_sequent oc hs =
  List.iter (p_assume oc) hs;
  fprintf oc "show FALSE\n";
;;

let p_name_hyps oc l =
  let pr e = fprintf oc "let \"?%s\" = \"%a\"\n" (getname e) p_expr e in
  List.iter pr l;
;;

let apply lam arg =
  match lam with
  | Elam (v, t, e1, _) -> substitute [(v, arg)] e1
  | _ -> assert false
;;

let rec p_tree oc proof =
  match proof.rule with
  | Rconnect (And, e1, e2) ->
     p_alpha oc "and" (eand (e1, e2)) [P e1; P e2] proof.hyps;
  | Rconnect (Or, e1, e2) ->
     p_beta oc "or" (eor (e1, e2)) [[P e1]; [P e2]] proof.hyps;
  | Rconnect (Imply, e1, e2) ->
     p_beta oc "imply" (eimply (e1, e2)) [[N e1]; [P e2]] proof.hyps;
  | Rconnect (Equiv, e1, e2) ->
     p_beta oc "equiv" (eequiv (e1, e2)) [[N e1; N e2]; [P e1; P e2]]
            proof.hyps;
  | Rnotconnect (And, e1, e2) ->
     p_beta oc "notand" (enot (eand (e1, e2))) [[N e1]; [N e2]] proof.hyps;
  | Rnotconnect (Or, e1, e2) ->
     p_alpha oc "notor" (enot (eor (e1, e2))) [N e1; N e2] proof.hyps;
  | Rnotconnect (Imply, e1, e2) ->
     p_alpha oc "notimply" (enot (eimply (e1, e2))) [P e1; N e2] proof.hyps;
  | Rnotconnect (Equiv, e1, e2) ->
     p_beta oc "notequiv" (enot (eequiv (e1, e2)))
            [[N e1; P e2]; [P e1; N e2]] proof.hyps;
  | Rextension (name, args, con, hs) ->
     let p_arg oc e = fprintf oc "\"%a\"" p_expr e in
     fprintf oc "proof (rule %s [of %a])\n" name (p_list "" p_arg " ") args;
     let rec p_sub l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          p_name_hyps oc h;
          p_sequent oc (List.map (fun x -> P x) h);
          p_tree oc t;
          fprintf oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub hs ts;
       | [], [] -> ()
       | _, _ -> assert false
     in
     p_sub hs proof.hyps;
  | Rnotnot (e1) ->
     p_alpha oc "notnot" (enot (enot e1)) [P e1] proof.hyps;
  | Rex (Eex (x, t, e1, _) as p, v) ->
     p_delta oc "ex" p v false (elam (x, t, e1)) proof.hyps;
  | Rex _ -> assert false
  | Rnotall (Eall (x, t, e1, _) as p, v) ->
     p_delta oc "notall" p v true (elam (x, t, e1)) proof.hyps;
  | Rnotall _ -> assert false
  | Rall (Eall (x, t, e1, _), e2) ->
     p_gamma oc "all" false (elam (x, t, e1)) e2 proof.hyps;
  | Rall _ -> assert false
  | Rnotex (Eex (x, t, e1, _), e2) ->
     p_gamma oc "notex" true (elam (x, t, e1)) e2 proof.hyps;
  | Rnotex _ -> assert false
  | Rlemma (l, a) ->
     fprintf oc "by (rule %s [of" l;
     List.iter (fun x -> fprintf oc " %s" x) a;
     fprintf oc "])\n";
  | Rcut (e1) ->
     fprintf oc "proof (rule zenon_em [of \"%a\"])\n" p_expr e1;
     let rec p_sub l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          p_name_hyps oc [e1];
          p_sequent oc h;
          p_tree oc t;
          fprintf oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub hs ts;
       | [], [] -> ()
       | _ -> assert false
     in p_sub [[P e1]; [N e1]] proof.hyps;
  | Raxiom (e1) ->
     let ne1 = getname e1 in
     let nne1 = getname (enot e1) in
     fprintf oc "apply (rule notE [OF %s %s])done\n" nne1 ne1;
  | Rdefinition (name, s, conc, hyp) ->
     let n_conc = getname conc in
     let n_hyp = getname hyp in
     fprintf oc "proof -\n";
     fprintf oc "have %s_%s: \"%a == %a\"\n" n_hyp n_conc
         p_expr hyp p_expr conc;
     fprintf oc "by (unfold %s)\n" name;
     fprintf oc "have %s: \"%a\"\n" n_hyp p_expr hyp;
     fprintf oc "by (unfold %s_%s, fact)\n" n_hyp n_conc;
     fprintf oc "show FALSE\n";
     begin match proof.hyps with
     | [t] -> p_tree oc t
     | _ -> assert false
     end;
     fprintf oc "qed\n";
  | Rnotequal _ -> assert false (* TODO *)
  | Rpnotp (Eapp (p, args1, _), (Enot (Eapp (q, args2, _), _) as np)) ->
     assert (p = q);
     fprintf oc "proof (rule notE [OF %s])\n" (getname np);
     list_iter3 (p_sub_equal oc) args1 args2 proof.hyps;
     let mk l = eapp (p, l) in
     p_subst oc mk args1 args2 [];
  | Rpnotp _ -> assert false
  | Rnoteq e1 ->
     let neq = enot (eapp ("=", [e1; e1])) in
     let n_neq = getname neq in
     fprintf oc "apply(rule zenon_noteq[OF %s])done\n" n_neq;
  | Rnottrue ->
     let nh = getname (enot etrue) in
     fprintf oc "apply(rule zenon_nottrue[OF %s])done\n" nh;
  | Rfalse ->
     fprintf oc "apply(rule %s)done\n" (getname efalse);

and p_alpha oc lem h0 hs sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let n0 = getname h0 in
  fprintf oc "proof (rule zenon_%s[OF %s])\n" lem n0;
  p_sequent oc hs;
  p_tree oc t;
  fprintf oc "qed\n";

and p_beta oc lem h0 hs sub =
  let n0 = getname h0 in
  fprintf oc "proof (rule zenon_%s[OF %s])\n" lem n0;
  let rec p_sub l1 l2 =
    match l1, l2 with
    | h::hs, t::ts ->
       p_sequent oc h;
       p_tree oc t;
       fprintf oc "%s\n" (if hs = [] then "qed" else "next");
       p_sub hs ts;
    | [], [] -> ()
    | _ -> assert false
  in
  p_sub hs sub;

and p_gamma oc lem neg lam e sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, ns) = if neg then (enot, "~") else ((fun x -> x), "") in
  let nlam = getname lam in
  let body = ng (apply lam e) in
  let nbody = getname body in
  fprintf oc "proof (rule zenon_%s[of \"?%s\" \"" lem nlam;
  p_expr oc e;
  fprintf oc "\"], assumption)\n";
  fprintf oc "assume %s: \"%s?%s " nbody ns nlam;
  p_expr oc e;
  fprintf oc "\"";
  p_is false oc body;
  fprintf oc "show FALSE\n";
  p_tree oc t;
  fprintf oc "qed\n";

and p_delta oc lem h0 v neg lam sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, ns) = if neg then (enot, "~") else ((fun x -> x), "") in
  let h00 = ng h0 in
  let n00 = getname h00 in
  fprintf oc "proof (rule zenon_%s[OF %s])\n" lem n00;
  fprintf oc "fix %s\n" v;
  let h =
    match lam with
    | Elam (x, _, e1, _) -> ng (substitute [(x, evar (v))] e1)
    | _ -> assert false
  in
  fprintf oc "assume %s: \"%a\"" (getname h) p_expr h;
  p_is false oc h;
  fprintf oc "show FALSE\n";
  p_tree oc t;

and p_sub_equal oc e1 e2 prf =
  let eq = eapp ("=", [e1; e2]) in
  if Expr.equal e1 e2
     || List.exists (Expr.equal eq) prf.conc
  then ()
  else begin
    let neq = enot (eq) in
    let n_e1 = getname e1 in
    let n_e2 = getname e2 in
    fprintf oc "have %s: \"%a = %a\"" (getname eq) p_expr e1 p_expr e2;
    p_is false oc eq;
    if List.exists (Expr.equal (eapp ("=", [e2; e1]))) prf.conc then begin
      fprintf oc "by (rule sym, fact)\n";
    end else begin
      fprintf oc "proof (rule zenon_nnpp [of \"?%s = ?%s\"])\n" n_e1 n_e2;
      fprintf oc "assume %s: \"?%s ~= ?%s\"\n" (getname neq) n_e1 n_e2;
      fprintf oc "show FALSE\n";
      p_tree oc prf;
      fprintf oc "qed\n";
    end;
  end;

and p_subst oc mk l1 l2 rl2 =
  match l1, l2 with
  | [], [] ->
     fprintf oc "thus \"?%s\" .\nqed\n" (getname (mk (List.rev rl2)));
  | h1 :: t1, h2 :: t2 ->
     let newrl2 = h2 :: rl2 in
     if Expr.equal h1 h2 then begin
       fprintf oc "let \"?%s\" = \"%a\"\n" (getname h1) p_expr h1;
     end else begin
       let args = List.rev_append newrl2 t1 in
       let e = mk args in
       let ghost = mk (List.map (fun e -> evar ("?" ^ getname e)) args) in
       let n_e = getname e in
       fprintf oc "have %s: \"%a\" (is \"?%s\")\n" n_e p_expr ghost n_e;
       let eq = eapp ("=", [h1; h2]) in
       fprintf oc "by (rule subst [OF %s], fact)\n" (getname eq);
     end;
     p_subst oc mk t1 t2 newrl2;
  | _, _ -> assert false
;;

let p_lemma oc lem =
  fprintf oc "lemma %s:\n" lem.name;
  List.iter (fun (x, y) -> fprintf oc " fixes \"%s\"\n" x) lem.params;
  let p_asm x =
    fprintf oc " assumes %s:\"" (getname x);
    p_expr oc x;
    fprintf oc "\"";
    p_is false oc x;
  in
  List.iter p_asm lem.proof.conc;
  fprintf oc " shows FALSE\n";
  p_tree oc lem.proof;
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

let p_theorem oc lem phrases =
  let ngoal = get_goal phrases in
  let goal =
    match ngoal with
    | Enot (e1, _) -> e1
    | _ -> assert false
  in
  let hyps = List.filter (fun x -> x <> ngoal) lem.proof.conc in
  let hypnames = mk_hyp_table phrases in
  let p_asm x =
    fprintf oc "have %s:\"%a\"" (getname x) p_expr x;
    p_is true oc x;
    begin match HE.find hypnames x with
    | "" -> fprintf oc "by fact\n"
    | n -> fprintf oc "by (rule %s)\n" n
    end
  in
  fprintf oc "proof (rule zenon_nnpp)\n";
  List.iter p_asm hyps;
  fprintf oc "let \"?%s\" = \"" (getname goal);
  p_expr oc goal;
  fprintf oc "\"\n";
  p_sequent oc [N goal];
  p_tree oc lem.proof;
  fprintf oc "qed\n";
;;

let rec p_lemmas oc llp phrases =
  match llp with
  | [] -> assert false
  | [x] -> p_theorem oc x phrases;
  | h::t -> p_lemma oc h; p_lemmas oc t phrases;
;;

let output oc phrases llp =
  if !Globals.ctx_flag then failwith "cannot output context in isar mode";
                                                                  (* TODO *)
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
  p_lemmas oc llp phrases;
  if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
  !Coqterm.constants_used
;;
