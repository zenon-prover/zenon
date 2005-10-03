(*  Copyright 2005 INRIA  *)
Version.add "$Id: context.ml,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $";;

open Expr;;
open Llproof;;
open Printf;;

type coqterm =
  | Cvar of string
  | Cty of string
  | Clam of string * coqterm * coqterm
  | Capp of coqterm * coqterm list
  | Cimply of coqterm * coqterm
  | Cequiv of coqterm * coqterm
  | Call of string * string * coqterm
  | Cex of string * string * coqterm
  | Clet of string * coqterm * coqterm
  | Cwild
;;

type coqproof =
  Phrase.phrase list * (string * coqterm) list * string * coqterm
;;

let lemma_env = (Hashtbl.create 97 : (string, coqterm) Hashtbl.t);;

let mapping = ref [];;

let getname e =
  let result = sprintf "_h%X" (Index.get_number e) in
  try List.assoc result !mapping
  with Not_found -> result
;;

let is_mapped e =
  let rawname = sprintf "_h%X" (Index.get_number e) in
  List.mem_assoc rawname !mapping
;;

let getv e = Cvar (getname e);;

let is_meta s = String.length s >= 3 && String.sub s 0 3 = "_Z_";;

exception Unused_variable of expr;;

(* For now, [synthesize] is very simple-minded. *)
let synthesize s =
  let len = String.length s in
  assert (len > 3);
  let i = int_of_string (String.sub s 3 (len - 3)) in
  let ty = match Index.get_formula i with
           | Eall (_, ty, _, _, _) | Enot (Eex (_, ty, _, _, _), _) -> ty
           | _ -> assert false
  in
  match ty with
  | "" | "_U" -> Cvar "_any"
  | "nat" -> Cvar "(0)"
  | _ -> raise (Unused_variable (Index.get_formula i))
;;

let rec trexpr e =
  match e with
  | Evar (v, _) when is_meta v -> synthesize v
  | Evar (v, _) -> Cvar v
  | Emeta (e1, _) -> assert false
  | Eapp (f, args, _) -> Capp (Cvar f, List.map trexpr args)
  | Enot (e1, _) -> Capp (Cvar "not", [trexpr e1])
  | Eand (e1, e2, _) -> Capp (Cvar "and", [trexpr e1; trexpr e2])
  | Eor (e1, e2, _) -> Capp (Cvar "or", [trexpr e1; trexpr e2])
  | Eimply (e1, e2, _) -> Cimply (trexpr e1, trexpr e2)
  | Eequiv (e1, e2, _) -> Cequiv (trexpr e1, trexpr e2)
  | Etrue -> Cvar "True"
  | Efalse -> Cvar "False"
  | Eall (Evar (v, _), t, e1, _, _) -> Call (v, t, trexpr e1)
  | Eall _ -> assert false
  | Eex (Evar (v, _), t, e1, _, _) -> Cex (v, t, trexpr e1)
  | Eex _ -> assert false
  | Etau _ -> assert false
;;

let tropt e = if !Globals.short_flag then Cwild else trexpr e;;
let trpred v ty p = Clam (v, Cty ty, trexpr p);;

let mklam v t = Clam (getname v, tropt v, t);;
let mklams args t = List.fold_right mklam args t;;

let rec common_prefix accu l1 l2 l3 =
  match l1, l2, l3 with
  | h1::t1, h2::t2, h3::t3 when Expr.equal h1 h2 ->
      common_prefix (h1::accu) t1 t2 t3
  | _, _, _ -> (List.rev accu, l1, l2, l3)
;;

let rec trtree node =
  let {conc = conc; rule = rule; hyps = hyps} = node in
  match rule with
  | Rfalse -> getv (efalse)
  | Rnottrue -> Capp (Cvar "zenon_nottrue", [getv (enot (etrue))])
  | Raxiom (p) -> Capp (getv (enot p), [getv p])
  | Rcut (p) ->
      let (subp, subnp) = tr_subtree_2 hyps in
      let lamp = mklam p subp in
      Clet (getname (enot p), lamp, subnp)
  | Rnoteq (e) ->
      let e_neq_e = getv (enot (eapp ("=", [e; e]))) in
      Capp (Cvar "zenon_noteq", [Cwild; trexpr e; e_neq_e])
  | Rnotnot (p) ->
      let sub = mklam p (tr_subtree_1 hyps) in
      Capp (getv (enot (enot p)), [sub])
  | Rconnect (And, p, q) ->
      let sub = mklam p (mklam q (tr_subtree_1 hyps)) in
      Capp (Cvar "zenon_and", [tropt p; tropt q; sub; getv (eand (p, q))])
  | Rconnect (Or, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam p subp in
      let lamq = mklam q subq in
      let concl = getv (eor (p, q)) in
      Capp (Cvar "zenon_or", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Imply, p , q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam q subq in
      let concl = getv (eimply (p, q)) in
      Capp (Cvar "zenon_imply", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam (enot q) sub1) in
      let lam2 = mklam p (mklam q sub2) in
      let concl = getv (eequiv (p, q)) in
      Capp (Cvar "zenon_equiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rnotconnect (And, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam (enot q) subq in
      let concl = getv (enot (eand (p, q))) in
      Capp (Cvar "zenon_notand", [tropt p; tropt q; lamp; lamq; concl])
  | Rnotconnect (Or, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam (enot p) (mklam (enot q) sub) in
      let concl = getv (enot (eor (p, q))) in
      Capp (Cvar "zenon_notor", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Imply, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam p (mklam (enot q) sub) in
      let concl = getv (enot (eimply (p, q))) in
      Capp (Cvar "zenon_notimply", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam q sub1) in
      let lam2 = mklam p (mklam (enot q) sub2) in
      let concl = getv (enot (eequiv (p, q))) in
      Capp (Cvar "zenon_notequiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rex (Eex (Evar (x, _) as vx, ty, px, _, _) as exp, z) ->
      let sub = tr_subtree_1 hyps in
      let pz = substitute [(vx, evar z)] px in
      let lam = Clam (z, Cty ty, mklam pz sub) in
      Capp (Cvar "zenon_ex", [Cty ty; trpred x ty px; lam; getv exp])
  | Rex _ -> assert false
  | Rnotall (Eall (Evar (x, _) as vx, ty, px, _, _) as allp, z) ->
      let sub = tr_subtree_1 hyps in
      let npz = enot (substitute [(vx, evar z)] px) in
      let lam = Clam (z, Cty ty, mklam npz sub) in
      let concl = getv (enot allp) in
      Capp (Cvar "zenon_notall", [Cty ty; trpred x ty px; lam; concl])
  | Rnotall _ -> assert false
  | Rall (Eall (Evar (x, _) as vx, ty, px, _, _) as allp, t) ->
      let sub = tr_subtree_1 hyps in
      let pt = substitute [(vx, t)] px in
      let lam = mklam pt sub in
      let p = trpred x ty px in
      let concl = getv allp in
      Capp (Cvar "zenon_all", [Cty ty; p; trexpr t; lam; concl])
  | Rall _ -> assert false
  | Rnotex (Eex (Evar (x, _) as vx, ty, px, _, _) as exp, t) ->
      let sub = tr_subtree_1 hyps in
      let npt = enot (substitute [(vx, t)] px) in
      let lam = mklam npt sub in
      let p = trpred x ty px in
      let concl = getv (enot (exp)) in
      Capp (Cvar "zenon_notex", [Cty ty; p; trexpr t; lam; concl])
  | Rnotex _ -> assert false
  | Rpnotp ((Eapp (p, args1, _) as pp),
            (Enot (Eapp (q, args2, _) as qq, _) as nqq)) ->
      assert (p = q);
      let (common, args1, args2, hyps) = common_prefix [] args1 args2 hyps in
      let pref = Capp (Cvar p, List.map trexpr common) in
      let peq = Capp (Cvar "zenon_equal_base", [Cwild; pref]) in
      let ppeqq = make_equals peq pref args1 pref args2 hyps in
      let vp = getv pp in
      let vnq = getv nqq in
      Capp (Cvar "zenon_pnotp", [tropt pp; tropt qq; ppeqq; vp; vnq])
  | Rpnotp _ -> assert false
  | Rnotequal ((Eapp (f, args1, _) as ff), (Eapp (g, args2, _) as gg)) ->
      assert (f = g);
      let (common, args1, args2, hyps) = common_prefix [] args1 args2 hyps in
      let pref = Capp (Cvar f, List.map trexpr common) in
      let feg = Capp (Cvar "zenon_equal_base", [Cwild; pref]) in
      let ffegg = make_equals feg pref args1 pref args2 hyps in
      let fdg = getv (enot (eapp ("=", [ff; gg]))) in
      let optf = tropt ff in
      let optg = tropt gg in
      Capp (Cvar "zenon_notequal", [Cwild; optf; optg; ffegg; fdg])
  | Rnotequal _ -> assert false
  | Requalnotequal (t, u, v, w) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let tdv = enot (eapp ("=", [t; v])) in
      let udv = enot (eapp ("=", [u; v])) in
      let udw = enot (eapp ("=", [u; w])) in
      let tdw = enot (eapp ("=", [t; w])) in
      let lam1 = mklam tdv (mklam udv sub1) in
      let lam2 = mklam udw (mklam tdw sub2) in
      let teu = getv (eapp ("=", [t; u])) in
      let vdw = getv (enot (eapp ("=", [v; w]))) in
      Capp (Cvar "zenon_equalnotequal",
            [Cwild; tropt t; tropt u; tropt v; tropt w; lam1; lam2; teu; vdw])
  | Rdefinition (folded, unfolded) ->
      let sub = tr_subtree_1 hyps in
      Clet (getname unfolded, getv folded, sub)
  | Rextension (name, args, c, hs) ->
      let metargs = List.map trexpr args in
      let hypargs = List.map2 mklams hs (List.map trtree hyps) in
      let conargs = List.map getv c in
      Capp (Cvar name, metargs @ hypargs @ conargs)
  | Rlemma (name, args) ->
      Hashtbl.find lemma_env name

and tr_subtree_1 l =
  match l with
  | [t] -> trtree t
  | _ -> assert false

and tr_subtree_2 l =
  match l with
  | [t1; t2] -> (trtree t1, trtree t2)
  | _ -> assert false

and make_equals peq p argsp q argsq hyps =
  match argsp, argsq, hyps with
  | [], [], [] -> peq
  | hp::tp, hq::tq, hh::th ->
      let thp = trexpr hp in
      let thq = trexpr hq in
      let lam = mklam (enot (eapp ("=", [hp; hq]))) (trtree hh) in
      let neweq = Capp (Cvar "zenon_equal_step",
                        [Cwild; Cwild; p; q; thp; thq; peq; lam])
      in
      let newp = Capp (p, [thp]) in
      let newq = Capp (q, [thq]) in
      make_equals neweq newp tp newq tq th
  | _, _, _ -> assert false
;;

let rec make_lambdas l term =
  match l with
  | [] -> term
  | (e, ty) :: t -> Clam (e, ty, make_lambdas t term)
;;

let rec rm_lambdas l term =
  match l, term with
  | [], _ -> term
  | _ :: t, Clam (_, _, e) -> rm_lambdas t e
  | _, _ -> assert false
;;

let compare_hyps (name1, _) (name2, _) = Pervasives.compare name1 name2;;

let make_lemma { name = name; params = params; proof = proof } =
  let hyps = List.filter (fun x -> not (is_mapped x)) proof.conc in
  let hyps0 = List.map (fun x -> (getname x, trexpr x)) hyps in
  let hyps1 = List.sort compare_hyps hyps0 in
  let pars = List.map (fun (x, y) -> (x, Cty y)) params in
  let formals = pars @ hyps1 in
  let actuals = List.map (fun (x, _) -> trexpr (evar x)) formals in
  (make_lambdas formals (trtree proof), name, actuals)
;;

let rec trp l =
  match l with
  | [th] ->
      let (thproof, thname, thargs) = make_lemma th
      in ([], rm_lambdas thargs thproof, thname, thargs)
  | h::t ->
      let (lem, name, args) = make_lemma h in
      Hashtbl.add lemma_env name (Capp (Cvar name, args));
      let (lemmas, thproof, thname, thargs) = trp t in
      ((name, lem) :: lemmas, thproof, thname, thargs)
  | [] -> assert false
;;

let rec make_mapping phrases =
  match phrases with
  | [] -> []
  | Phrase.Hyp (n, e, _) :: t -> (getname e, n) :: (make_mapping t)
  | Phrase.Def _ :: t -> make_mapping t
;;

let rec get_goal phrases =
  match phrases with
  | [] -> None
  | Phrase.Hyp ("_Zgoal", e, _) :: _ -> Some e
  | _ :: t -> get_goal t
;;

let rec get_th_name lemmas =
  match lemmas with
  | [] -> assert false
  | [h] -> h.name
  | _ :: t -> get_th_name t
;;

let trproof phrases l =
  try
    Hashtbl.clear lemma_env;
    mapping := make_mapping phrases;
    let (lemmas, raw, th_name, formals) = trp l in
    match get_goal phrases with
    | Some goal ->
        let term = Capp (Cvar "NNPP", [Cwild; Clam ("_Zgoal", tropt goal, raw)])
        in
        (phrases, lemmas, th_name, term)
    | None -> (phrases, lemmas, th_name, raw)
  with
  | Unused_variable e ->
      begin
        let v = match e with
        | Eall (Evar (v, _), _, _, _, _)
        | Enot (Eex (Evar (v, _), _, _, _, _), _)
          -> v
        | _ -> assert false
        in
        eprintf "Error: unused variable %s in:\n" v;
        Print.expr (Print.Chan stderr) e;
        flush stderr;
        raise (Failure "unused variable");
      end
;;

(* ******************************************* *)

let line_len = 72;;

let rem_len = ref line_len;;
let buf = Buffer.create 100;;
exception Cut_before of int;;
exception Cut_at of int;;

let test_cut j c =
  match c with
  | '('|')'|'~'|'>'|','|'['|']'|'?' -> raise (Cut_before (j+1))
  | ':'|'<' -> raise (Cut_before j)
  | ' ' -> raise (Cut_at j)
  | _ -> ()
;;
let init_buf () = rem_len := line_len;;
let flush_buf oc =
  let s = Buffer.contents buf in
  let len = String.length s in
  let i = ref 0 in
  while !i + !rem_len <= len do
    try
      for j = !rem_len - 1 downto 0 do
        test_cut j s.[!i + j];
      done;
      if !rem_len < line_len then raise (Cut_before 0);
      for j = !rem_len to len - !i - 1 do
        test_cut j s.[!i + j];
      done;
      raise (Cut_before (len - !i))
    with
    | Cut_before j ->
        output oc s !i j;
        i := !i + j;
        output_char oc '\n';
        rem_len := line_len;
    | Cut_at j ->
        output oc s !i j;
        i := !i + j + 1;
        output_char oc '\n';
        rem_len := line_len;
  done;
  output oc s !i (len - !i);
  rem_len := !rem_len - (len - !i);
  Buffer.clear buf;
;;

let rec get_lams accu t =
  match t with
  | Clam (s, ty, t1) -> get_lams ((s, ty) :: accu) t1
  | _ -> (List.rev accu, t)
;;

let make_lemma_type t =
  let (tys, _) = get_lams [] t in
  let make_funtype (v, ty1) ty2 =
    match ty1 with
    | Cty ty -> Call (v, ty, ty2)
    | _ -> Cimply (ty1, ty2)
  in
  List.fold_right make_funtype tys (Cty "False")
;;

(* ******************************************* *)

let pr_oc oc prefix t =
  let rec pr b t =
    match t with
    | Cvar "" -> assert false
    | Cvar s -> bprintf b "%s" s; flush_buf oc;
    | Cty s -> bprintf b "%a" pr_ty s;
    | Clam (s, Cwild, t2) -> bprintf b "(fun %s=>%a)" s pr t2;
    | Clam (_, _, Clam _) ->
        let (lams, body) = get_lams [] t in
        bprintf b "(fun%a=>%a)" pr_lams lams pr body;
    | Clam (s, t1, t2) -> bprintf b "(fun %s:%a=>%a)" s pr t1 pr t2;
    | Capp (Cvar "=", [t1; t2]) -> bprintf b "(%a=%a)" pr t1 pr t2;
    | Capp (Cvar "not", [t1]) -> bprintf b "(~%a)" pr t1;
    | Capp (Cvar "and", [t1;t2]) -> bprintf b "(%a/\\%a)" pr t1 pr t2;
    | Capp (Cvar "or", [t1;t2]) -> bprintf b "(%a\\/%a)" pr t1 pr t2;
    | Capp (t1, []) -> pr b t1;
    | Capp (Capp (t1, args1), args2) -> pr b (Capp (t1, args1 @ args2));
    | Capp (t1, args) -> bprintf b "(%a%a)" pr t1 pr_list args;
    | Cimply (t1, t2) -> bprintf b "(%a->%a)" pr t1 pr t2;
    | Cequiv (t1, t2) -> bprintf b "(%a<->%a)" pr t1 pr t2;
    | Call (v, ty, t1) -> bprintf b "(forall %s:%a,%a)" v pr_ty ty pr t1;
    | Cex (v, ty, t1) -> bprintf b "(exists %s:%a,%a)" v pr_ty ty pr t1;
    | Clet (v, t1, t2) -> bprintf b "(let %s:=%a in %a)" v pr t1 pr t2;
    | Cwild -> bprintf b "_";

  and pr_list b l =
    let f t = bprintf b " %a" pr t; in
    List.iter f l;

  and pr_lams b l =
    let f (v, ty) =
      match ty with
      | Cwild -> bprintf b " %s" v;
      | _ -> bprintf b "(%s:%a)" v pr ty;
    in
    List.iter f l;

  and pr_ty b t =
    match t with
    | "" -> bprintf b "_U";
    | "?" -> bprintf b "_";
    | s -> bprintf b "(%s)" s;
  in

  init_buf ();
  bprintf buf "%s" prefix;
  pr buf t;
  flush_buf oc;
;;

let print_lemma oc (name, t) =
  let prefix = sprintf "Let %s:" name in
  pr_oc oc prefix (make_lemma_type t);
  fprintf oc ".\n";
  pr_oc oc "Proof " t;
  fprintf oc ".\n";
;;

let print_theorem oc (name, t) =
  let prefix = sprintf "Definition %s:=" name in
  pr_oc oc prefix t;
  fprintf oc ".\n";
;;

type result = Prop | Term | Indirect of string;;
type signature = int * result;;

let get_signatures ps =
  let symtbl = (Hashtbl.create 97 : (string, signature) Hashtbl.t) in
  let defined = ref ["="] in
  let add_sig sym arity kind =
    if not (Hashtbl.mem symtbl sym) then
      Hashtbl.add symtbl sym (arity, kind)
  in
  let rec get_sig r env e =
    match e with
    | Evar (s, _) -> if not (List.mem s env) then add_sig s 0 r;
    | Emeta _ | Etrue | Efalse -> ()
    | Eapp (s, args, _) ->
        add_sig s (List.length args) r;
        List.iter (get_sig Term env) args;
    | Eand (e1, e2, _) | Eor (e1, e2, _)
    | Eimply (e1, e2, _) | Eequiv (e1, e2, _)
      -> get_sig Prop env e1;
         get_sig Prop env e2;
    | Enot (e1, _) -> get_sig Prop env e1;
    | Eall (Evar (v, _), _, e1, _, _) | Eex (Evar (v, _), _, e1, _, _)
    | Etau (Evar (v, _), _, e1, _)
      -> get_sig Prop (v::env) e1;
    | Eall _ | Eex _ | Etau _ -> assert false
  in
  let do_phrase p =
    match p with
    | Phrase.Hyp (_, e, _) -> get_sig Prop [] e;
    | Phrase.Def (DefReal (s, _, e)) ->
        defined := s :: !defined;
        get_sig (Indirect s) [] e;
    | _ -> assert false
  in
  List.iter do_phrase ps;
  let rec follow_indirect path s =
    if List.mem s path then Prop else
      begin try
        match Hashtbl.find symtbl s with
        | (_, ((Prop|Term) as kind)) -> kind
        | (_, Indirect s1) -> follow_indirect (s::path) s1
      with Not_found -> Prop
      end
  in
  let find_sig sym sign l =
    if List.mem sym !defined then l
    else begin
      match sign with
      | (arity, ((Prop|Term) as kind)) -> (sym, arity, kind) :: l
      | (arity, Indirect s) -> (sym, arity, follow_indirect [] s) :: l
    end
  in
  Hashtbl.fold find_sig symtbl []
;;

let print_signature oc (sym, arity, kind) =
  let rec print_arity n =
    if n = 0 then () else begin
      fprintf oc "_U -> ";
      print_arity (n-1);
    end;
  in
  fprintf oc "Parameter %s : " sym;
  print_arity arity;
  match kind with
  | Prop -> fprintf oc "Prop.\n";
  | Term -> fprintf oc "_U.\n";
  | Indirect _ -> assert false;
;;

let declare_hyp oc h =
  match h with
  | Phrase.Hyp ("_Zgoal", _, _) -> ()
  | Phrase.Hyp (name, stmt, _) ->
      pr_oc oc (sprintf "Parameter %s : " name) (trexpr stmt);
      fprintf oc ".\n";
  | Phrase.Def (DefReal (sym, params, body)) ->
      assert false (* FIXME TODO recuperer les types des params *)
  | Phrase.Def _ -> assert false
;;

let declare_coq_context oc phrases =
  if !Globals.ctx_flag then begin
    if not !Globals.quiet_flag then fprintf oc "(* BEGIN-CONTEXT *)\n";
    fprintf oc "Require Import zenon.\n";
    (* FIXME TODO import lemmas for extensions *)
    fprintf oc "Parameter _U : Set.\n";
    fprintf oc "Parameter _any : _U.\n";
    let sigs = get_signatures phrases in
    List.iter (print_signature oc) sigs;
    List.iter (declare_hyp oc) phrases;
    if not !Globals.quiet_flag then fprintf oc "(* END-CONTEXT *)\n";
  end
;;