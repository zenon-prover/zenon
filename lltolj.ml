open Printf;;
open Expr;;
open Llproof;;
open Namespace;;

type sequent = expr list * expr list

type tree = {
  cconc : expr list;
  cgamma : expr list;
  crule : rule; 
  chyps : tree list; 
  ccontr : expr list;
};;

type lkrule =
| SCaxiom of expr
| SCfalse
| SCtrue
| SCeqref of expr
| SCeqsym of expr * expr
| SCeqprop of expr * expr
| SCeqfunc of expr * expr
| SCrweak of expr * lkproof
| SClcontr of expr * lkproof
| SCcut of expr * lkproof * lkproof
| SCland of expr * expr * lkproof
| SClor of expr * expr * lkproof * lkproof
| SClimply of expr * expr * lkproof * lkproof
| SClnot of expr * lkproof
| SClall of expr * expr * lkproof
| SClex of expr * expr * lkproof
| SCrand of expr * expr * lkproof * lkproof
| SCrorl of expr * expr * lkproof
| SCrorr of expr * expr * lkproof
| SCrimply of expr * expr * lkproof
| SCrnot of expr * lkproof
| SCrall of expr * expr * lkproof
| SCrex of expr * expr * lkproof
| SCcnot of expr * lkproof

and lkproof = 
  expr list * expr * lkrule
;;

let lemma_env = 
  (Hashtbl.create 97 : (string, prooftree) Hashtbl.t)
;;

let distinct_terms = ref [];;

let hypothesis_env = ref [];;

let definition_env =
  (Hashtbl.create 97 : (string, expr list * expr) Hashtbl.t)
;;

let new_terms = ref [];;


let rew_env = ref ((Hashtbl.create 97 : (string, expr * expr) Hashtbl.t),
		   (Hashtbl.create 97 : (string, expr * expr) Hashtbl.t));;

let new_var = 
  let r = ref 0 in
  fun () -> 
    let n = !r in
    incr r;
    evar (sprintf "v%d" n)
;;

let p_debug s es = 
  eprintf "%s |" s;
  List.iter
    (eprintf " %a |" 
       (fun oc x -> Print.expr (Print.Chan oc) x)
    ) es; 
  eprintf "\n";
;;

let p_debug_proof s (g, c, rule) =
  eprintf "%s : gamma = |" s;
  List.iter
    (eprintf " %a |" 
       (fun oc x -> Print.expr (Print.Chan oc) x)) g; 
  eprintf "\n and conc = |";
  eprintf " %a |" 
    (fun oc x -> Print.expr (Print.Chan oc) x) c;
  eprintf "\n";
;;

let p_debug_seq s (g, c, rule) = 
  eprintf "%s |" s;
  List.iter
    (eprintf " %a |" 
       (fun oc x -> Print.expr (Print.Chan oc) x)) g; 
  eprintf "- ";
  eprintf " %a" 
    (fun oc x -> Print.expr (Print.Chan oc) x) c;
  eprintf "\n";
;;

let rec p_debug_llproof s proof = 
  eprintf "%s :\n" s;
  let rec p_iter s proof =
    p_debug s (proof.cconc @ proof.cgamma);
    List.iter (p_iter ("  "^s)) proof.chyps in
  p_iter "" proof;
  eprintf "\n";
;;

let rec p_debug_llprf s proof = 
  eprintf "%s :\n" s;
  let rec p_iter s proof =
    p_debug s (proof.conc);
    List.iter (p_iter ("  "^s)) proof.hyps in
  p_iter "" proof;
  eprintf "\n";
;;

let equalmod e1 e2 = 
  let f1 = Rewrite.normalize_fm (!rew_env) e1 in
  let f2 = Rewrite.normalize_fm (!rew_env) e2 in
  (*if Expr.equal f1 f2
  then p_debug "equal" [e1; e2]
  else p_debug "not equal" [e1; e2];*)
  Expr.equal f1 f2
;;

let rec inlist e l =
  (*p_debug "test e" [e];
  p_debug "in l" l;*)
  match l with
  | [] -> false
  | x :: q -> equalmod e x || inlist e q
;;

let ingamma e proof =
  let g, c, rule = proof in
  List.exists (equal e) g
;;

let sd list =
  match list with
  | x :: l -> List.hd l
  | _ -> assert false
;;

let rec freevar x e =
  match e with
  | Evar _ when equal e x -> true
  | Evar _ -> false
  | Eapp (_, args, _) -> List.exists (freevar x) args
  | Etrue | Efalse -> false
  | Enot (e, _) -> freevar x e
  | Eand (e1, e2, _) -> freevar x e1 || freevar x e2
  | Eor (e1, e2, _) -> freevar x e1 || freevar x e2
  | Eimply (e1, e2, _) -> freevar x e1 || freevar x e2
  | Eall (y, _, e, _) -> if equal y x then false else freevar x e
  | Eex (y, _, e, _) -> if equal y x then false else freevar x e
  | _ -> assert false
;;

let make_node proofs rule = 
  {conc = []; hyps = proofs; rule = rule}
;;

let rec xhypstoadd rule =
  match rule with
  | Rfalse -> [], [efalse]
  | Rnottrue -> [], [enot etrue]
  | Raxiom (p) -> [], [p; enot p]
  | Rcut (p) -> [[p]; [enot p]], []
  | Rnoteq (a) -> [], [enot (eapp ("=", [a; a]))]
  | Reqsym (a, b) -> 
    [], [eapp ("=", [a; b]); enot (eapp ("=", [b; a]))]
  | Rnotnot (p) -> [[p]], [enot (enot p)]
  | Rconnect (b, p, q) -> 
    begin match b with
    | And -> [[p; q]], [eand (p, q)]
    | Or -> [[p]; [q]], [eor (p, q)]
    | Imply -> [[enot p]; [q]], [eimply (p, q)]
    | Equiv -> assert false end
  | Rnotconnect (b, p, q) ->
    begin match b with
    | And -> [[enot p]; [enot q]], [enot (eand (p, q))]
    | Or -> [[enot p; enot q]], [enot (eor (p, q))]
    | Imply -> [[p; enot q]], [enot (eimply (p, q))]
    | Equiv -> assert false end
  | Rex (ep, v) -> 
    begin match ep with
    | Eex (x, ty, p, _) -> [[substitute [(x, v)] p]], [ep]
    | _ -> assert false end
  | Rall (ap, t) -> 
    begin match ap with
    | Eall (x, ty, p, _) -> [[substitute [(x, t)] p]], [ap]
    | _ -> assert false end
  | Rnotex (ep, t) -> 
    begin match ep with
    | Eex (x, ty, p, _) -> 
      [[enot (substitute [(x, t)] p)]], [enot ep]
    | _ -> assert false end
  | Rnotall (ap, v) -> 
    begin match ap with
    | Eall (x, ty, p, _) -> 
      [[enot (substitute [(x, v)] p)]], [enot ap]
    | _ -> assert false end
  | Rpnotp (e1, e2) -> 
    begin match e1, e2 with
    | Eapp (p, ts, _), Enot (Eapp (q, us, _), _) ->
      List.map2 
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us, 
      [e1; e2]
    | _ -> assert false end
  | Rnotequal (e1, e2) -> 
    begin match e1, e2 with
    | Eapp (p, ts, _), Eapp (q, us, _) ->
      List.map2 
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us, 
      [enot (eapp ("=", [e1; e2]))]
    | _ -> assert false end
  | RcongruenceLR (p, a, b) -> 
    [[apply p b]], [apply p a; eapp ("=", [a; b])]
  | RcongruenceRL (p, a, b) -> 
    [[apply p b]], [apply p a; eapp ("=", [b; a])]
  | Rextension (ext, name, args, concs, hyps) ->
    hyps, concs
  | Rlemma (name, args) ->
    assert false;
  | _ -> assert false 

and hypstoadd rule = 
  let l1, l2 = xhypstoadd rule in
  List.map (List.map use_defs) l1, List.map use_defs l2

and use_defs expr = 
  let e = Rewrite.normalize_fm (!rew_env) expr in
  match e with
  | Evar (v, _) when Hashtbl.mem definition_env v -> 
    let (params, body) = Hashtbl.find definition_env v in
    body
  | Eapp (s, args, _) when Hashtbl.mem definition_env s ->
    let exprs = List.map use_defs args in
    let (params, body) = Hashtbl.find definition_env s in
    substitute (List.combine params exprs) body
  | Evar _ | Etrue | Efalse -> e
  | Eapp (s, args, _) ->
    eapp (s, List.map use_defs args)
  | Enot (e, _) ->
    enot (use_defs e)
  | Eand (e1, e2, _) ->
    eand (use_defs e1, use_defs e2)
  | Eor (e1, e2, _) ->
    eor (use_defs e1, use_defs e2)
  | Eimply (e1, e2, _) ->
    eimply (use_defs e1, use_defs e2)
  | Eequiv (e1, e2, _) ->
    let expr1 = use_defs e1 in
    let expr2 = use_defs e2 in
    eand (eimply (expr1, expr2), eimply (expr2, expr1))
  | Eall (x, s, e, _) ->
    eall (x, s, use_defs e)
  | Eex (x, s, e, _) ->
    eex (x, s, use_defs e)
  | Etau (x, s, e, _) ->
    let tau = etau (x, s, use_defs e) in
    if List.mem_assoc tau !new_terms
    then List.assoc tau !new_terms
    else
      let z = new_var () in
      new_terms := (tau, z) :: !new_terms;
      z
  | Elam (x, s, e, _) ->
    elam (x, s, use_defs e)
  | Emeta (x, _) ->
    assert false;
;;

let rec xcongruence_elim s x e a b =
  match e with
  | Evar (v, _) when equal e x ->
    if s
    then make_node [] (Raxiom (eapp ("=", [a; b])))
    else make_node [] (Reqsym (a, b))
  | Evar _ -> make_node [] (Rnoteq e)
  | Eapp (_, args, _) -> 
    make_node 
      (List.map (fun arg -> xcongruence_elim s x arg a b) args) 
      (Rnotequal (substitute [(x, a)] e, substitute [(x, b)] e))
  | Etrue | Efalse | Enot _ | Eand _ | Eor _ | Eimply _
  | Eall _ | Eex _ | Eequiv _ | Etau _ | Elam _ | Emeta _ 
    -> assert false
;; 

let rec congruence_elim s x e a b =
  match e with
  | Evar _ -> make_node [] (Raxiom e)
  | Eapp (_, args, _) -> 
    make_node 
      (List.map (fun arg -> xcongruence_elim s x arg a b) args) 
      (Rpnotp (substitute [(x, a)] e, enot (substitute [(x, b)] e)))
  | Etrue -> make_node [] Rnottrue
  | Efalse -> make_node [] Rfalse
  | Enot (f, _) ->
    make_node [congruence_elim (not s) x f b a]
      (Rnotnot (substitute [(x, b)] f))
  | Eand (f1, f2, _) ->
    make_node [
      make_node 
	[congruence_elim s x f1 a b; congruence_elim s x f2 a b]
	(Rnotconnect (And, f1, f2))]
      (Rconnect (And, f1, f2))
  | Eor (f1, f2, _) ->
    make_node [
      make_node [congruence_elim s x f1 a b] 
	(Rnotconnect (Or, f1, f2));
      make_node [congruence_elim s x f2 a b]
	(Rnotconnect (Or, f1, f2))]
      (Rconnect (Or, f1, f2))
  | Eimply (f1, f2, _) ->
    make_node [
      make_node
	[congruence_elim (not s) x f1 b a; 
	 congruence_elim s x f2 a b] (Rconnect (Imply, f1, f2))]
      (Rnotconnect (Imply, f1, f2))
  | Eall (y, ty, f, _) ->
    let v = use_defs (etau (y, ty, enot f)) in
    let g = substitute [(y, v)] f in
    make_node [make_node [congruence_elim s x g a b] (Rall (e, v))]
      (Rnotall (e, v))
  | Eex (y, ty, f, _) ->
    let v = use_defs (etau (y, ty, f)) in
    let g = substitute [(y, v)] f in
    make_node [
      make_node [congruence_elim s x g a b] 
	(Rnotex (e, v))] 
      (Rex (e, v))
  | Eequiv _ | Etau _ | Elam _ | Emeta _ -> assert false
;;

let rec notallex_elim proof ap ep y nq = 
  match proof.rule with
  | Rex (e, v) when (equal e ep) ->
    make_node proof.hyps 
      (Rnotall (ap, y))
  | Raxiom e when (equal e ep) -> 
    make_node [
      make_node [make_node [] (Raxiom nq)] (Rnotex (ep, y))]
      (Rnotall (ap, y))
  | _ ->
    let hyps, _ = hypstoadd proof.rule in
    make_node 
      (List.map2 
	 (fun prf list -> 
	   if inlist ep list 
	   then prf
	   else notallex_elim prf ap ep y nq) 
	 proof.hyps hyps)
      proof.rule
;;

let rec use_defs_rule rule =
  match rule with
  | Rfalse -> Rfalse
  | Rnottrue -> Rnottrue
  | Raxiom (p) -> Raxiom (use_defs p)
  | Rcut (p) -> Rcut (use_defs p)
  | Rnoteq (a) -> Rnoteq (use_defs a)
  | Reqsym (a, b) -> Reqsym (use_defs a, use_defs b)
  | Rnotnot (p) -> Rnotnot (use_defs p)
  | Rconnect (b, p, q) -> Rconnect (b, use_defs p, use_defs q) 
  | Rnotconnect (b, p, q) -> 
    Rnotconnect (b, use_defs p, use_defs q)
  | Rex (ep, v) -> Rex (use_defs ep, use_defs v) 
  | Rall (ap, t) -> Rall (use_defs ap, use_defs t)
  | Rnotex (ep, t) -> Rnotex (use_defs ep, use_defs t)
  | Rnotall (ap, v) -> Rnotall (use_defs ap, use_defs v)
  | Rpnotp (e1, e2) -> Rpnotp (use_defs e1, use_defs e2) 
  | Rnotequal (e1, e2) -> Rnotequal (use_defs e1, use_defs e2)
  | Rdefinition (name, sym, args, body, recarg, c, h) -> 
    rule
  | Rextension (ext, name, args, cons, hyps) ->
    Rextension (
      ext, name, List.map use_defs args, 
      List.map use_defs cons, List.map (List.map use_defs) hyps)
  | Rroot (e) -> Rroot (use_defs e)
  | Rlemma _ -> assert false
  | RcongruenceLR _ -> assert false
  | RcongruenceRL _ -> assert false
 

;;

let rec llapplyinrule f rule =
  match rule with
  | Rfalse -> Rfalse
  | Rnottrue -> Rnottrue
  | Raxiom (p) -> Raxiom (f p)
  | Rcut (p) -> Rcut (f p)
  | Rnoteq (a) -> Rnoteq (f a)
  | Reqsym (a, b) -> Reqsym (f a, f b)
  | Rnotnot (p) -> Rnotnot (f p)
  | Rconnect (b, p, q) -> Rconnect (b, f p, f q) 
  | Rnotconnect (b, p, q) -> 
    Rnotconnect (b, f p, f q)
  | Rex (ep, v) -> Rex (f ep, f v) 
  | Rall (ap, t) -> Rall (f ap, f t)
  | Rnotex (ep, t) -> Rnotex (f ep, f t)
  | Rnotall (ap, v) -> Rnotall (f ap, f v)
  | Rpnotp (e1, e2) -> Rpnotp (f e1, f e2) 
  | Rnotequal (e1, e2) -> Rnotequal (f e1, f e2)
  | Rdefinition (name, sym, args, body, recarg, c, h) -> 
    rule
  | Rextension (ext, name, args, cons, hyps) ->
    Rextension (
      ext, name, List.map f args, 
      List.map f cons, List.map (List.map f) hyps)
  | Rlemma _ -> assert false
  | RcongruenceLR _ -> assert false
  | RcongruenceRL _ -> assert false
  | Rroot (e) -> Rroot (f e)
;;

let llchange_vars proof =
  let rec xchange env proof =
    let subs e = substitute env e in
    match proof.rule with
    | Rex (ep, v) -> 
      let nv = new_var () in
      make_node (List.map (xchange ((v, nv) :: env)) proof.hyps)
	(Rex (subs ep, nv))
    | Rnotall (ap, v) -> 
      let nv = new_var () in
      make_node (List.map (xchange ((v, nv) :: env)) proof.hyps)
	(Rnotall (subs ap, nv))
    | _ -> 
      make_node (List.map (xchange env) proof.hyps)
	(llapplyinrule subs proof.rule)
  in xchange [] proof
;;

let rec use_defs_proof proof = 
  match proof.rule with
  | Rconnect (Equiv, p, q) ->
    let a = use_defs p in
    let b = use_defs q in
    let hyp1, hyp2 = 
      match proof.hyps with
      | [h1; h2] -> use_defs_proof h1, use_defs_proof h2
      | _ -> assert false in
    make_node 
      [make_node 
	  [make_node [hyp1; make_node [] (Raxiom a)]
	      (Rconnect (Imply, b, a)); 
	   make_node [make_node [] (Raxiom b); hyp2]
	     (Rconnect (Imply, b, a))]
	  (Rconnect (Imply, a, b))]
      (Rconnect (And, eimply (a, b), eimply (b, a)))
  | Rnotconnect (Equiv, p, q) -> 
    let a = use_defs p in
    let b = use_defs q in
    let hyp1, hyp2 = 
      match proof.hyps with
      | [h1; h2] -> use_defs_proof h1, use_defs_proof h2
      | _ -> assert false in
    make_node 
      [make_node [hyp2] (Rnotconnect (Imply, a, b)); 
       make_node [hyp1] (Rnotconnect (Imply, b, a))]
      (Rnotconnect (And, eimply (a, b), eimply (b, a)))
  | Rlemma (name, args) ->
    llchange_vars
      (use_defs_proof (Hashtbl.find lemma_env name))
  | Rdefinition _ ->
    begin match proof.hyps with
    | [prf] -> use_defs_proof proof
    | _ -> assert false end
  | RcongruenceLR (Elam (x, _, p, _) as lam, a, b) ->
    make_node 
      [use_defs_proof proof; 
       congruence_elim true x (use_defs p) 
	 (use_defs a) (use_defs b)]
      (Rcut (use_defs (apply lam b)))
  | RcongruenceRL (Elam (x, _, p, _) as lam, a, b) ->
    make_node 
      [use_defs_proof proof; 
       congruence_elim false x (use_defs p) 
	 (use_defs a) (use_defs b)]
      (Rcut (use_defs (apply lam b)))      
  | Rextension ("", "zenon_notallex", [Elam (v, t, p, _)], 
		[Enot (ap, _)], [[ep]]) ->
    let prf = use_defs_proof (List.hd proof.hyps) in
    let y = use_defs (etau (v, t, enot p)) in
    let q = substitute [(v, y)] (use_defs p) in
    notallex_elim prf (use_defs ap) (use_defs ep) y (enot q)
  | Rroot (p) -> 
    begin match proof.hyps with
    | [hyp] -> use_defs_proof hyp
    | _ -> assert false end
  | _ ->
    make_node (List.map use_defs_proof proof.hyps)
      (use_defs_rule proof.rule)
;;

let rec rm a list =
  match list with
  | x :: list when equal (use_defs x) (use_defs a) -> list
  | x :: list -> x :: (rm a list)
  | [] -> assert false
;;

let scaxiom (e, g) = e :: g, e, SCaxiom e;;
let scfalse (g, e) = efalse :: g, e, SCfalse;;
let sctrue (g) = g, etrue, SCtrue;;
let sceqref (a, g) = g, eapp ("=", [a; a]), SCeqref (a);;
let sceqsym (a, b, g) =
  eapp ("=", [a; b]) :: g, eapp ("=", [b; a]), SCeqsym (a, b);;
let sceqprop (e1, e2, g) =
  match e1, e2 with
  | Eapp (p, ts, _), Eapp (q, us, _) when p = q ->
    e1 :: g @ List.map2 (fun t u -> eapp ("=", [t; u])) ts us, e2, 
    SCeqprop (e1, e2)
  | _, _ -> assert false
let sceqfunc (e1, e2, g) =
  match e1, e2 with
  | Eapp (p, ts, _), Eapp (q, us, _) when p = q ->
    g @ List.map2 (fun t u -> eapp ("=", [t; u])) ts us, 
    eapp ("=", [e1; e2]), SCeqfunc (e1, e2)
  | _, _ -> assert false
let scrweak (e, proof) =
  let g, c, rule = proof in
  (*p_debug_proof "fail with sequent" proof*)
  (*assert (equal c efalse);*)
  if (equal e efalse)
  then proof
  else g, e, SCrweak (e, proof);;
let sclcontr (e, proof) =
  let g, c, rule = proof in
  (*p_debug "\n contract element" [e];
  p_debug_proof "\n in list" proof;*)
  (*assert (inlist e g);*)
  (*assert (inlist e (rm e g));*)
  rm e g, c, SClcontr (e, proof)
let sccut (e, proof1, proof2) = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  (*assert (List.length g2 = List.length g1 + 1);*)
  (*assert (equal c1 e);*)
  g1, c2, SCcut(e, proof1, proof2);;
let scland (e1, e2, proof) = 
  (*assert (ingamma e2 proof);*)
  let (g, c, rule) = proof in
  (*assert (inlist e1 (rm e2 g));*)
  (eand (e1, e2)) :: rm e1 (rm e2 g), c, SCland (e1, e2, proof);;
let sclor (e1, e2, proof1, proof2) = 
  (*assert (ingamma e1 proof1);*)
  let (g1, c, rule1) = proof1 in
  (*let (g2, _, _) = proof2 in
  assert (List.length g2 = List.length g1);*)
  (eor (e1, e2)) :: rm e1 g1, c, SClor (e1, e2, proof1, proof2);;
let sclimply (e1, e2, proof1, proof2) = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  (*assert (List.length g2 = List.length g1 + 1);*)
  (eimply (e1, e2)) :: g1, c2, 
  SClimply (e1, e2, proof1, proof2);;
let sclnot (e, proof) = 
  let (g, d, rule) = proof in
  (*assert (equal e d);*)
  (enot e) :: g, efalse, SClnot (e, proof);;
let sclall (e1, t, proof) = 
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, c, rule) = proof in
    let q = substitute [(x, t)] p in
    let f = use_defs q in
    (*p_debug "fail : q" [q];
    p_debug "with f" [f];
    p_debug "not in list" g;*)
    (*assert (ingamma f proof);*)
    e1 :: rm f g, c, SClall (e1, t, proof)
  | _ -> assert false;;
let sclex (e1, v, proof) = 
  match e1 with
  | Eex (x, ty, p, _) ->
    let (g, c, rule) = proof in
    let q = substitute [(x, v)] p in
    (*assert (ingamma q proof);*)
    (*List.iter (fun e -> assert (not (freevar v e))) 
      (c :: (rm q g));*)
    e1 :: rm q g, c, SClex (e1, v, proof)
  | _ -> assert false;;
let scrand (e1, e2, proof1, proof2) = 
  let (g1, d1, rule1) = proof1 in
  (*let (g2, _, _) = proof2 in
  assert (List.length g2 = List.length g1);*)
  g1, eand (e1, e2), SCrand (e1, e2, proof1, proof2);;
let scrorl (e1, e2, proof) = 
  let (g, d, rule) = proof in
  g, eor (e1, e2), SCrorl (e1, e2, proof);;
let scrorr (e1, e2, proof) = 
  let (g, d, rule) = proof in
  g, eor (e1, e2), SCrorr (e1, e2, proof);;
let scrimply (e1, e2, proof) = 
  (*assert (ingamma e1 proof);*)
  let (g, d, rule) = proof in
  rm e1 g, eimply (e1, e2), SCrimply (e1, e2, proof);;
let scrnot (e, proof) = 
  (*assert (ingamma e proof);*)
  let (g, d, rule) = proof in
  rm e g, enot e, SCrnot (e, proof);;
let scrall (e1, v, proof) = 
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, c, rule) = proof in
    (*List.iter (fun e -> assert (not (freevar v e))) g;*)
    g, e1, SCrall (e1, v, proof)
  | _ -> assert false;;
let screx (e1, t, proof) = 
  match e1 with
  | Eex (x, ty, p, _) ->
    let (g, c, rule) = proof in
    g, e1, SCrex (e1, t, proof)
  | _ -> assert false;;
let sccnot (e, proof) = 
  let (g, c, rule) = proof in
  (*assert (equal c efalse);*)
  (*assert (inlist (enot e) g);*)
  rm (enot e) g, e, SCcnot (e, proof);;

let gamma_length (g, c, rule) = List.length g;;

let hypsofrule lkrule =
  match lkrule with
  | SCaxiom (e) -> []
  | SCfalse -> []
  | SCtrue -> []
  | SCeqref (e) -> []
  | SCeqsym (e1, e2) -> []
  | SCeqprop (e1, e2) -> []
  | SCeqfunc (e1, e2) -> []
  | SCrweak (e, proof) -> [proof]
  | SClcontr (e, proof) -> [proof]
  | SCcut (e, proof1, proof2) -> [proof1; proof2]
  | SCland (e1, e2, proof) -> [proof]
  | SClor (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClimply (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClnot (e, proof) -> [proof]
  | SClall (e1, e2, proof) -> [proof]
  | SClex (e1, e2, proof) -> [proof]
  | SCrand (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SCrorl (e1, e2, proof) -> [proof]
  | SCrorr (e1, e2, proof) -> [proof]
  | SCrimply (e1, e2, proof) -> [proof]
  | SCrnot (e, proof) -> [proof]
  | SCrall (e1, e2, proof) -> [proof]
  | SCrex (e1, e2, proof) -> [proof]
  | SCcnot (e, proof) -> [proof]
;;

let rec p_debug_lkproof s proof =
  eprintf "%s :\n" s;
  let rec p_iter s proof =
    let _, _, rule = proof in
    p_debug_seq s proof;
    List.iter (p_iter ("  "^s)) (hypsofrule rule) in
  p_iter "" proof;
  eprintf "\n";
;;

let applytohyps f lkproof =
  let g, c, lkrule = lkproof in
  match lkrule with
  | SCaxiom (e) -> g, c, SCaxiom (e)
  | SCfalse -> g, c, SCfalse
  | SCtrue -> g, c, SCtrue
  | SCeqref (e) -> g, c, SCeqref (e)
  | SCeqsym (e1, e2) -> g, c, SCeqsym (e1, e2)
  | SCeqprop (e1, e2) -> g, c, SCeqprop (e1, e2)
  | SCeqfunc (e1, e2) -> g, c, SCeqfunc (e1, e2)
  | SCrweak (e, proof) -> scrweak (e, f proof)
  | SClcontr (e, proof) -> sclcontr (e, f proof)
  | SCcut (e, proof1, proof2) ->
    sccut (e, f proof1, f proof2)
  | SCland (e1, e2, proof) ->
    scland (e1, e2, f proof)
  | SClor (e1, e2, proof1, proof2) ->
    sclor (e1, e2, f proof1, f proof2)
  | SClimply (e1, e2, proof1, proof2) ->
    sclimply (e1, e2, f proof1, f proof2)
  | SClnot (e, proof) -> sclnot (e, f proof)
  | SClall (e1, e2, proof) -> sclall (e1, e2, f proof)
  | SClex (e1, e2, proof) -> sclex (e1, e2, f proof)
  | SCrand (e1, e2, proof1, proof2) ->
    scrand (e1, e2, f proof1, f proof2)
  | SCrorl (e1, e2, proof) -> 
    scrorl (e1, e2, f proof)
  | SCrorr (e1, e2, proof) ->
    scrorr (e1, e2, f proof)
  | SCrimply (e1, e2, proof) ->
    scrimply (e1, e2, f proof)
  | SCrnot (e, proof) -> scrnot (e, f proof)
  | SCrall (e1, e2, proof) -> scrall (e1, e2, f proof)
  | SCrex (e1, e2, proof) -> screx (e1, e2, f proof)
  | SCcnot (e, proof) -> sccnot (e, f proof)
;;

let applytohyps2 fs lkproof =
  let g, c, lkrule = lkproof in
  match lkrule, fs with
  | SCaxiom (e), [] -> g, c, SCaxiom (e)
  | SCfalse, [] -> g, c, SCfalse
  | SCtrue, [] -> g, c, SCtrue
  | SCeqref (e), [] -> g, c, SCeqref (e)
  | SCeqsym (e1, e2), [] -> g, c, SCeqsym (e1, e2)
  | SCeqprop (e1, e2), [] -> g, c, SCeqprop (e1, e2)
  | SCeqfunc (e1, e2), [] -> g, c, SCeqfunc (e1, e2)
  | SCrweak (e, proof), [f] -> scrweak (e, f proof)
  | SClcontr (e, proof), [f] -> sclcontr (e, f proof)
  | SCcut (e, proof1, proof2), [f1; f2] ->
    sccut (e, f1 proof1, f2 proof2)
  | SCland (e1, e2, proof), [f] ->
    scland (e1, e2, f proof)
  | SClor (e1, e2, proof1, proof2), [f1; f2] ->
    sclor (e1, e2, f1 proof1, f2 proof2)
  | SClimply (e1, e2, proof1, proof2), [f1; f2] ->
    sclimply (e1, e2, f1 proof1, f2 proof2)
  | SClnot (e, proof), [f] -> sclnot (e, f proof)
  | SClall (e1, e2, proof), [f] -> sclall (e1, e2, f proof)
  | SClex (e1, e2, proof), [f] -> sclex (e1, e2, f proof)
  | SCrand (e1, e2, proof1, proof2), [f1; f2] ->
    scrand (e1, e2, f1 proof1, f2 proof2)
  | SCrorl (e1, e2, proof), [f] -> 
    scrorl (e1, e2, f proof)
  | SCrorr (e1, e2, proof), [f] ->
    scrorr (e1, e2, f proof)
  | SCrimply (e1, e2, proof), [f] ->
    scrimply (e1, e2, f proof)
  | SCrnot (e, proof), [f] -> scrnot (e, f proof)
  | SCrall (e1, e2, proof), [f] -> scrall (e1, e2, f proof)
  | SCrex (e1, e2, proof), [f] -> screx (e1, e2, f proof)
  | SCcnot (e, proof), [f] -> sccnot (e, f proof)
  | _, _ -> assert false
;;

let applytohyps3 f fe lkproof =
  let g, c, lkrule = lkproof in
  match lkrule with
  | SCaxiom (e) -> 
    List.map fe g, fe c, SCaxiom (fe e)
  | SCfalse -> 
    List.map fe g, fe c, SCfalse
  | SCtrue -> 
    List.map fe g, fe c, SCtrue
  | SCeqref (e) -> 
    List.map fe g, fe c, SCeqref (fe e)
  | SCeqsym (e1, e2) -> 
    List.map fe g, fe c, SCeqsym (fe e1, fe e2)
  | SCeqprop (e1, e2) -> 
    List.map fe g, fe c, SCeqprop (fe e1, fe e2)
  | SCeqfunc (e1, e2) -> 
    List.map fe g, fe c, SCeqfunc (fe e1, fe e2)
  | SCrweak (e, proof) -> scrweak (fe e, f proof)
  | SClcontr (e, proof) -> sclcontr (fe e, f proof)
  | SCcut (e, proof1, proof2) ->
    sccut (fe e, f proof1, f proof2)
  | SCland (e1, e2, proof) ->
    scland (fe e1, fe e2, f proof)
  | SClor (e1, e2, proof1, proof2) ->
    sclor (fe e1, fe e2, f proof1, f proof2)
  | SClimply (e1, e2, proof1, proof2) ->
    sclimply (fe e1, fe e2, f proof1, f proof2)
  | SClnot (e, proof) -> sclnot (fe e, f proof)
  | SClall (e1, e2, proof) -> sclall (fe e1, fe e2, f proof)
  | SClex (e1, e2, proof) -> sclex (fe e1, fe e2, f proof)
  | SCrand (e1, e2, proof1, proof2) ->
    scrand (fe e1, fe e2, f proof1, f proof2)
  | SCrorl (e1, e2, proof) -> 
    scrorl (fe e1, fe e2, f proof)
  | SCrorr (e1, e2, proof) ->
    scrorr (fe e1, fe e2, f proof)
  | SCrimply (e1, e2, proof) ->
    scrimply (fe e1, fe e2, f proof)
  | SCrnot (e, proof) -> scrnot (fe e, f proof)
  | SCrall (e1, e2, proof) -> scrall (fe e1, fe e2, f proof)
  | SCrex (e1, e2, proof) -> screx (fe e1, fe e2, f proof)
  | SCcnot (e, proof) -> sccnot (fe e, f proof)
;;

let rec xaddhyp h lkproof =
  let g, c, lkrule = lkproof in 
  match lkrule with
  | SCaxiom _ | SCfalse 
  | SCtrue | SCeqref _ | SCeqsym _ 
  | SCeqprop _ | SCeqfunc _ -> 
    h :: g, c, lkrule
  | _ -> applytohyps (xaddhyp h) lkproof
    
and addhyp hyps lkproof =
  List.fold_left (fun pf h -> xaddhyp h pf) lkproof hyps
;;  

let sceqpropbis (e1, e2, proofs, gamma) = 
  (*List.iter (fun proof ->
    p_debug "\ngamma" gamma;
    p_debug_proof "proof" proof;
    assert (List.length gamma = gamma_length proof)) proofs;*)
  match e1, e2 with
  | Eapp (_, ts, _), Eapp (_, us, _) ->
    let prf0 = sceqprop (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2 
	(fun (l, prf) eq proof ->
	  (*assert (inlist eq l);*)
	  let hyps = rm eq l in
	  (*assert (gamma_length prf = 
	     gamma_length (addhyp hyps proof) + 1);*)
	  hyps, sccut (eq, addhyp hyps proof, prf))
	(e1 :: eqs, prf0) eqs proofs in
    proof
  | _, _ -> assert false
;;
let sceqfuncbis (e1, e2, proofs, gamma) =
  match e1, e2 with
  | Eapp (_, ts, _), Eapp (_, us, _) ->
    let prf0 = sceqfunc (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2 
	(fun (l, prf) eq proof ->
	  (*assert (inlist eq l);*)
	  let hyps = rm eq l in
	  (*assert (gamma_length prf = 
	     gamma_length (addhyp hyps proof) + 1);*)
	  hyps, sccut (eq, addhyp hyps proof, prf))
	(eqs, prf0) eqs proofs in
    proof
  | _, _ -> assert false
;;

let rec oneinlist a l =
  match l with
  | [] -> false
  | x :: q when (equal x a) ->
    not (inlist a q)
  | x :: q -> oneinlist a q
;;

(*----------------------------------------------------------*)

let change_vars proof =
  let rec xchange env proof =
    let subs e = substitute env e in
    let _, _, rule = proof in
    match rule with
    | SClex (ep, v, proof) -> 
      let nv = new_var () in
      sclex (subs ep, nv, xchange ((v, nv) :: env) proof)
    | SCrall (ap, v, proof) -> 
      let nv = new_var () in
      scrall (subs ap, nv, xchange ((v, nv) :: env) proof)
    | _ -> applytohyps3 (xchange env) subs proof
  in xchange [] proof
;;

let rec union lists = 
  match lists with
  | [] -> [], []
  | [list] -> list, [[]]
  | [] :: lists -> 
    let main, remainders = union lists in
    main, main :: remainders
  | (x :: l) :: lists ->
    let main, remainders = union (l :: lists) in
    match remainders with
    | remainder :: remainders ->
      if inlist x main 
      then 
	if inlist x remainder
	then main, (rm x remainder) :: remainders
	else main, remainder :: remainders
      else
	x :: main, 
	remainder :: (List.map (fun xs -> x :: xs) remainders)
    | _ -> assert false
;;

let rec lladdhyp l prf =
  {cconc = prf.cconc;
   cgamma = l @ prf.cgamma; 
   chyps = List.map (lladdhyp l) prf.chyps;
   crule = prf.crule;
   ccontr = prf.ccontr}
;;

let rec clean e proof =
  (*assert (inlist e proof.cgamma || inlist e proof.cconc);*)
  let gamma = proof.cgamma in
  let hyps = proof.chyps in
  let hypslist, _ = hypstoadd proof.crule in
  let result1 = 
    if inlist e gamma 
    then
      let list = List.fold_left 
	(fun hypos hypolist -> 
	  List.fold_left
	    (fun partial hypo -> 
	      (List.map (fun l -> l@[hypo]) hypos) @ partial)
	    [] hypolist)
	[[]] (List.map (xclean e) hyps) in
      List.map
	(fun l ->
	  {cconc = proof.cconc;
	    cgamma = rm e proof.cgamma; 
	    chyps = l;
	    crule = proof.crule;
	    ccontr = 
	      if inlist e proof.ccontr
	      then rm e proof.ccontr
	      else proof.ccontr}) list
    else [] in
  if inlist e proof.cconc
  then
    let result2 = 
      List.flatten (
	List.map2
	  (fun prf l ->
	    let others = rm e proof.cconc in
	    List.map (lladdhyp others)
	      (List.fold_left
		 (fun prfs f -> List.flatten (
		   List.map (xclean f) prfs))
		 [prf] l))
	  hyps hypslist) in
    result1 @ result2
  else result1

and xclean e proof = 
    if inlist e proof.ccontr
    then 
      List.flatten (List.map (clean e) (clean e proof))
    else
      clean e proof  
;;

let rec addcontrs proof gamma =
  let hypslist, conclist = hypstoadd proof.rule in
  let newcontr, list =
    List.fold_left (fun (cs, es) e -> 
      if (inlist e es) 
      then
	((*p_debug "e" [e];
	 p_debug "is in list" es;*)
	 cs, rm e es)
      else
	((*p_debug "e" [e];
	 p_debug "is not in list" es;*)
	 e :: cs, es))
      ([], gamma) conclist in
  let contrshyps = List.map2 addcontrs proof.hyps
    (List.map (List.rev_append list) hypslist) in
  let contrs, prehyps = List.split contrshyps in
  let maincontr, remainders = union contrs in
  let hyps = List.map2 lladdhyp remainders prehyps in
  let (contracted, remaining) =
    List.fold_left
      (fun (contracted, remaining) c ->
	if inlist c conclist
	then 
	  ((*p_debug "c" [c];
	   p_debug "is in conclist" conclist;*)
	   c :: contracted, remaining)
	else 
	  ((*p_debug "c" [c];
	   p_debug "is not in conclist" conclist;*)
	   contracted, c :: remaining)
      )
      ([], newcontr) maincontr in
(*  p_debug_llproof "" 
    {cconc = conclist;
     cgamma = list@maincontr;
     chyps = hyps;
     crule = proof.rule;
     ccontr = contracted};*)
  remaining, {
    cconc = conclist;
    cgamma = list@maincontr;
    chyps = hyps;
    crule = proof.rule;
    ccontr = contracted}
;;

let rec deduce_inequality e1 e2 v1 v2 c1 c2 b1 b2 gamma proof =
  let n1 = List.assoc v1 !distinct_terms in
  let n2 = List.assoc v2 !distinct_terms in
  let eq = eapp ("=", [e1; e2]) in
  let b3 = n1 < n2 in
  let ax = 
    if b3
    then eapp ("=", [v1; v2])
    else eapp ("=", [v2; v1]) in
  let rec f b1 b2 b3 = 
    match b1, b2, b3 with
    | true, true, true -> sceqprop (eq, ax, [])
    | _, _, false -> 
      sccut (
	eapp ("=", [v1; v2]),
	f b1 b2 true, sceqsym (v1, v2, [c1; c2; eq]))
    | _, false, _ -> 
      sccut (
	eapp ("=", [e2; v2]),
	sceqsym (v2, e2, [c1; eq]), addhyp [c2] (f b1 true b3))
    | false, _, _ ->
      sccut (
	eapp ("=", [e1; v1]),
	sceqsym (v1, e1, [c2; eq]), addhyp [c1] (f true b2 b3))
  in
  sccut (
    enot eq,
    addhyp (rm (enot ax) gamma) (
      scrnot (eq, sclnot (ax, (f b1 b2 b3)))),
    addhyp [c1; c2] proof)
;;

let rec addtogamma proof =
  let _, _, rule = proof in
  match rule with
  | SClnot (e, _) -> enot e
  | SClimply (e1, e2, _, _) -> eimply (e1, e2)
  | SCland (e1, e2, _) -> eand (e1, e2)
  | SClor (e1, e2, _, _) -> eor (e1, e2)
  | SClall (e, _, _) -> e
  | SClex (e, _, _) -> e
  | _ -> assert false
;;
      
let rec removeinhyps proof =
  let _, _, rule = proof in
  match rule with
  | SCcnot (e, _) -> [[enot e]]
  | SCrimply (e1, _, _) -> [[e1]]
  | SCrnot (e, _) -> [[e]]
  | SClcontr (e, _) -> [[e]]
  | SCrand _ -> [[]; []]
  | SCrweak _ | SCrorl _ | SCrorr _ | SCrall _ | SCrex _ -> [[]]
  | SClnot (e, _) -> [[]]
  | SClimply (e1, e2, _, _) -> [[];[e2]]
  | SCland (e1, e2, _) -> [[e1; e2]]
  | SClor (e1, e2, _, _) -> [[e1]; [e2]]
  | SClall (Eall (x, _, e, _), t, _) -> [[substitute [(x, t)] e]]
  | SClex (Eex (x, _, e, _), v, _) -> [[substitute [(x, v)] e]] 
  | SCcut (e, _, _) -> [[]; [e]]
  | _ -> assert false
;;

let rec ntimes n e1 e2 g =
  (*assert (inlist e2 g);*)
  if n = 1 then e1 :: (rm e2 g)
  else e1 :: (rm e2 (ntimes (n-1) e1 e2 g))
;;

let rec ntimeslist n l e2 g =
  (*assert (inlist e2 g);*)
  if n = 1 then l @ (rm e2 g)
  else l @ (rm e2 (ntimeslist (n-1) l e2 g))
;;

(* transforme proof = gamma, enot p |- c en 
   gamma, big |- c
   avec cons : prf delta |- p => prf delta, big |- *)
let rec adaptproof proof p big cons =
  let rec xmake proof n = 
    let g, c, rule = proof in
    match rule with
    | SClnot (e, prf) when (equal e p) ->
      if n = 1 then cons prf else cons (xmake prf (n-1))
    | SClcontr (e, prf) when (equal e (enot p) && 
	n = List.length (List.filter (equal (enot p)) g)) ->
      sclcontr (big, xmake prf (n+1))
    | SCaxiom e when (equal e (enot p) && 
        n = List.length (List.filter (equal (enot p)) g)) ->
      scrnot (p, xmake (sclnot (p, scaxiom (p, rm e g))) n)
    | SClnot _ | SCland _ | SClor _ | SClall _ | SClex _ | SCrweak _
    | SCcnot _ | SCrimply _ | SCrnot _ | SClcontr _ | SClimply _ 
    | SCrand _ | SCrorl _ | SCrorr _ | SCrall _ | SCrex _ | SCcut _
      -> 
      applytohyps2 (List.map (
	fun hs -> (fun prf -> xmake prf n)) (removeinhyps proof)) 
	proof
    | SCaxiom _ | SCfalse | SCtrue | SCeqref _ 
    | SCeqsym _ | SCeqprop _ | SCeqfunc _ 
      -> (ntimes n big (enot p) g), c, rule in
  xmake proof 1
;;
      
(* transforme proof1 = gamma, enot p |- c en 
   gamma, big |- c
   avec proof2 = gamma, x |- y
   cons : prf delta |- p, prf delta, x |- y => prf delta, big |- *)
let rec makeproof proof1 proof2 p big cons =
  let prf2 = change_vars proof2 in
  let rec xmake proof l1 l2 n = 
    let g, c, rule = proof in
    match rule with
    | SClnot (e, prf) when (equal e p) ->
      if n = 1 then
	cons (addhyp l1 prf) (addhyp l2 prf2)
      else
	cons (xmake prf l1 (rm big l2) (n-1)) (addhyp l2 prf2)
    | SClcontr (e, prf) when (equal e (enot p) && 
	n = List.length (List.filter (equal (enot p)) g)) ->
      sclcontr (big, xmake prf l1 (big :: l2) (n+1))
    | SCaxiom e when (equal e (enot p) && 
        n = List.length (List.filter (equal (enot p)) g)) ->
      scrnot (
	p, xmake (sclnot (
	  p, scaxiom (p, rm e g))) l1 (p :: l2) n)
    | SClnot _ | SClimply _ | SCland _ | SClor _ 
    | SClall _ | SClex _
      -> 
      let e = addtogamma proof in
      if inlist e l2
      then
	applytohyps2 (List.map (
	  fun hs -> (fun prf -> xmake prf l1 (hs @ (rm e l2)) n)) ( 
	  removeinhyps proof)) proof
      else
	sclcontr (e, applytohyps2 (List.map (
	  fun hs -> (fun prf -> xmake prf (e :: l1) (hs @ l2) n)) ( 
	  removeinhyps proof)) proof)
    | SCcnot _ | SCrimply _ | SCrnot _ | SClcontr _ | SCrweak _ 
    | SCrand _ | SCrorl _ | SCrorr _ | SCrall _ | SCrex _ | SCcut _
      -> applytohyps2 (List.map (
	fun hs -> (fun prf -> xmake prf l1 (hs @ l2) n)) (
	removeinhyps proof)) proof
    | SCaxiom _ | SCfalse | SCtrue | SCeqref _ 
    | SCeqsym _ | SCeqprop _ | SCeqfunc _ 
      -> (ntimes n big (enot p) g)@l1, c, rule in
  xmake proof1 [] [] 1
;;

let rec make_imply p q proof1 proof2 =
  makeproof proof1 proof2 p (eimply (p, q)) 
    (fun prf1 prf2 -> sclimply (p, q, prf1, prf2))
(* (gamma, not p |- c), (gamma, not q |- ) *)
;;
let rec make_not_and_l p q proof1 proof2 =
  makeproof proof1 proof2 p (enot (eand (p, q))) 
    (fun prf1 prf2 -> 
      makeproof prf2 prf1 q (enot (eand (p, q))) 
	(fun pr1 pr2 -> 
	  sclnot (eand (p, q), scrand (p, q, pr2, pr1))))
;;
let rec make_not_and_r p q proof1 proof2 =
  makeproof proof2 proof1 q (enot (eand (p, q))) 
    (fun prf1 prf2 -> 
      makeproof prf2 prf1 p (enot (eand (p, q))) 
	(fun pr1 pr2 -> 
	  sclnot (eand (p, q), scrand (p, q, pr1, pr2))))
;;
let rec make_not_or p q proof =
  sclcontr (
    enot (eor (p, q)), 
    adaptproof 
      (adaptproof proof q (enot (eor (p, q)))
	 (fun prf -> sclnot (eor (p, q), scrorr (p, q, prf))))
      p (enot (eor (p, q)))
      (fun prf -> sclnot (eor (p, q), scrorl (p, q, prf))))
;;
let rec make_not_imply1 p q proof =
  sclcontr (enot (eimply (p, q)), sclnot (
    eimply (p, q), scrimply (p, q, scrweak (
      q, adaptproof proof q (enot (eimply (p, q)))
	(fun prf -> sclnot (
	  eimply (p, q), scrimply (p, q, addhyp [p] prf)))))))
;;
let rec make_not_imply2 p q proof =
  adaptproof proof q (enot (eimply (p, q)))
    (fun prf -> sclnot (
      eimply (p, q), scrimply (p, q, addhyp [p] prf)))
;;
let rec make_not_exists sub ep t proof =
  adaptproof proof sub (enot ep)
    (fun prf -> sclnot (ep, screx (ep, t, prf)))
;;
    
let rec righttoleft e proof =
  let g, c, rule = proof in
  let ne = enot e in
  match rule with
  | SCcnot (f, prf) -> prf
  | SClnot _ -> assert false
  | SClimply (f1, f2, prf1, prf2) ->
    sclimply (f1, f2, xaddhyp ne prf1, righttoleft e prf2)
  | SCcut (f, prf1, prf2) ->
    sccut (f, xaddhyp ne prf1, righttoleft e prf2)
  | SCland _ | SClor _ | SClall _ | SClex _
    -> applytohyps (righttoleft e) proof
  | SCaxiom _ | SCfalse | SCtrue | SCeqref _ | SCeqsym _
  | SCeqprop _ | SCeqfunc _ | SCrweak _
    -> sclnot (e, proof)
  | SCrand _ | SCrorl _ | SCrorr _ 
  | SCrimply _ | SCrnot _ | SCrall _ | SCrex _ | SClcontr _
    -> sclnot (e, proof)
;;

let rec lefttoright e proof =
  let g, c, rule = proof in
  let ne = enot e in
  (*assert (inlist ne g);*)
  (*assert (lkuseful ne proof); only in the beginning*)
  match e with
  | Enot (f, _) -> assert false
    (*optimize (scrnot (f, rmdblnot f proof))*)
  | _ -> 
    (*assert (equal c efalse);*)
    (*assert (ingamma ne proof);*)
    match rule with
    | SClnot (f, prf) 
	when (equal f e) -> prf
    | SClcontr (f, _) 
	when (equal ne f) -> sccnot (e, proof)
    | SClimply (a, b, prf1, prf2)
	when (not (lkuseful ne prf1)) ->
      sclimply (a, b, lkclean ne prf1, lefttoright e prf2)
    | SCcut (a, prf1, prf2)
	when (not (lkuseful ne prf1)) ->
      sccut (a, lkclean ne prf1, lefttoright e prf2)
    | SClnot _ | SCcut _ | SClimply _ -> 
      sccnot (e, proof)
    | SCaxiom _ | SCfalse -> 
      scfalse (rm efalse (rm ne g), e)
    | SClcontr _ | SClor _ | SCland _ | SClex _ | SClall _
      -> applytohyps (lefttoright e) proof
    | SCrex _ | SCrall _ | SCrand _ | SCrorr _ | SCrorl _
    | SCrimply _ | SCrnot _ | SCeqfunc _ | SCeqprop _ 
    | SCeqsym _ | SCeqref _ | SCtrue | SCcnot _ | SCrweak _
      -> assert false	  

and optimize proof =
  let g, c, rule = proof in
  match rule with
  | SCcnot (e, prf) ->
    lefttoright e prf
  | SClnot (e, prf) -> 
    righttoleft e prf
  | _ -> applytohyps optimize proof

and lkclean f prf = 
  let g, c, rule = prf in
  match rule with
  | SCeqsym _ | SCeqref _ 
  | SCtrue | SCaxiom _ | SCfalse
  | SCeqprop _ | SCeqfunc _ -> 
    (*assert (inlist f g);*)
    rm f g, c, rule
  | _ -> applytohyps (lkclean f) prf

and lkuseful e proof =
  let g, c, rule = proof in
  match rule with
  | SCeqsym (a, b) -> 
    equal e (eapp ("=", [a; b])) && not (inlist e (rm e g))
  | SCeqref (a) -> false
  | SCtrue -> false
  | SCaxiom (a) -> equal e a && not (inlist e (rm e g))
  | SCfalse -> equal e efalse && not (inlist e (rm e g))
  | SCeqprop (Eapp (p, ts, _) as f1, Eapp (_, us, _)) ->
    let x = equal e f1 in
    List.fold_left2 
      (fun x t u -> (x || equal e (eapp ("=", [t; u]))))
      x ts us
  | SCeqprop _ -> assert false
  | SCeqfunc (Eapp (p, ts, _), Eapp (_, us, _)) ->
    List.fold_left2 
      (fun x t u -> (x || equal e (eapp ("=", [t; u]))))
      false ts us 
  | SCeqfunc _ -> assert false
  | SClcontr (f, _) 
      when (equal e f && not (inlist e (rm e g))) -> true
  | SClor (a, b, _, _) 
      when (equal e (eor (a, b)) 
	    && not (inlist e (rm e g))) -> true
  | SCland (a, b, _)
      when (equal e (eand (a, b)) 
	    && not (inlist e (rm e g))) -> true
  | SClex (f, _, _)
      when (equal e f && not (inlist e (rm e g))) -> true
  | SClall (f, _, _)
      when (equal e f && not (inlist e (rm e g))) -> true
  | SClnot (f, _)
      when (equal e (enot f) && not (inlist e (rm e g))) -> true
  | SClimply (a, b, _, _)
      when (equal e (eimply (a, b))
	    && not (inlist e (rm e g))) -> true
  | SClcontr _ | SClor _ | SCland _ | SClex _
  | SClall _ | SClnot _ | SClimply _ | SCcut _
  | SCrimply _ | SCrnot _ | SCrex _ | SCrall _ 
  | SCrand _ | SCrorr _ | SCrorl _ | SCrweak _ | SCcnot _
    -> List.exists (lkuseful e) (hypsofrule rule)
;;

let equalrule rule1 rule2 =
  match rule1, rule2 with
  | Rconnect (binop1, a1, b1), Rconnect (binop2, a2, b2) ->
    binop1 = binop2 && equal a1 a2 && equal b1 b2
  | _ -> false
;;

let make_cnode rule hyps gamma =
  let _, conc = hypstoadd rule in
  {cconc = conc;
   cgamma = gamma;
   chyps = hyps;
   crule = rule;
   ccontr = []}
;;

let deeper_axiom proof =
  let gamma = proof.cgamma in
  match proof.crule with
  | Raxiom e ->
    begin match e with
    | Eand (a, b, _) ->
      make_cnode (Rconnect (And, a, b))
	[make_cnode (Rnotconnect (And, a, b))
	    [make_cnode (Raxiom a) [] (b :: enot b :: gamma);
	     make_cnode (Raxiom b) [] (a :: enot a :: gamma);] 
	    (enot a :: enot b :: gamma)] (enot e :: gamma)	
    | Eor (a, b, _) ->
      make_cnode (Rconnect (Or, a, b))
	[make_cnode (Rnotconnect (Or, a, b))
	    [make_cnode (Raxiom a) [] (enot b :: gamma)]
	    (e :: gamma);
	 make_cnode (Rnotconnect (Or, a, b))
	   [make_cnode (Raxiom b) [] (enot a :: gamma)]
	   (e :: gamma)]
	(enot e :: gamma)
    | _ -> assert false end
  | _ -> assert false
;;

let replaceinproof nb e ab rule proof = 
  let rec xmake proof n = 
    match proof.crule with
    | xrule when (equalrule rule xrule) ->
      let m = if proof.ccontr = [] then n else n + 1 in
      if m = 1 then (List.nth proof.chyps nb) 
      else xmake (List.nth proof.chyps nb) (m - 1)
    | Raxiom x when (equal e x && 
       n - 1 = List.length (List.filter (equal e) proof.cgamma)) -> 
      xmake (deeper_axiom proof) n
    | _ ->
	{cconc = proof.cconc;
	 cgamma = ntimeslist n ab e proof.cgamma;
	 chyps = List.map (fun prf -> xmake prf n) proof.chyps;
	 crule = proof.crule;
	 ccontr = proof.ccontr}
  in 
  let m = if proof.ccontr = [] then 1 else 2 in
  xmake proof m
;;

let permuterules proof right = 
  let seq = proof.cconc @ proof.cgamma in
  let rec permuteleft proof l =
    match l with
    | x :: l -> 
      begin match x with
      | Eor (a, b, _) -> 
	let rule = Rconnect (Or, a, b) in
	let prf = 
	  make_cnode rule 
	    [replaceinproof 0 (eor (a, b)) [a] rule proof; 
	     replaceinproof 1 (eor (a, b)) [b] rule proof]
	    (rm (eor (a, b)) seq) in
	Some prf
      | Eand (a, b, _) ->
	let rule = Rconnect (And, a, b) in
	let prf = 
	  make_cnode rule 
	    [replaceinproof 0 (eand (a, b)) [a; b] rule proof]
	    (rm (eand (a, b)) seq) in
	Some prf
      | _ -> permuteleft proof l end
    | [] -> None in
  let permuteright proof right =
    match right with
    | Enot (e, _) ->
      let rule = Rnotnot e in
      let prf = 
	make_cnode rule
	  [replaceinproof 0 (enot (enot e)) [e] rule proof]
	  (rm (enot (enot e)) seq) in
      Some prf
    | _ ->  None in
  match permuteright proof right with
  | Some prf -> Some prf
  | None -> permuteleft proof proof.cgamma
;;

let rec tryconstructive proof r contr = 
  match permuterules proof r with
  | Some prf -> 
    if contr
    then lltolkrule prf [r]
    else xlltolkrule prf [r]
  | None -> 
    if contr
    then lefttoright r (lltolkrule proof [])
    else lefttoright r (xlltolkrule proof [])

and xlltolkrule llproof right =
  let gamma = llproof.cgamma in
  match llproof.crule, llproof.chyps, right with
  | Rfalse, [], [] ->
    scfalse (gamma, efalse)
  | Rfalse, [], [r] ->
    scfalse (rm (enot r) gamma, r)
  | Rnottrue, [], [] ->
    righttoleft etrue (sctrue (gamma))
  | Rnottrue, [], [Etrue] ->
    sctrue (gamma)
  | Rnottrue, [], [r] ->
    scrweak (r, sclnot (etrue, sctrue (rm (enot r) gamma)))
  | Raxiom p, [], [] -> 
    righttoleft p (scaxiom (p, gamma))
  | Raxiom p, [], [r] ->
    if equal r p
    then scaxiom (p, gamma)
    else if not (equal (enot r) p) 
    then scrweak (r, sclnot (p, scaxiom (p, rm (enot r) gamma)))
    else tryconstructive llproof r false
  | Rcut p, [proof1; proof2], [] ->
    let prf1 = lltolkrule proof1 [] in
    let prf2 = lltolkrule proof2 [] in
    sccut (enot p, scrnot (p, prf1), prf2)
  | Rcut p, [proof1; proof2], [r] ->
    let cleans1 = clean (enot r) proof1 in
    if not (cleans1 = [])
    then 
      let prf1 = lltolkrule (List.hd cleans1) [] in
      let prf2 = lltolkrule proof2 [r] in
      sccut (enot p, scrnot (p, prf1), prf2)
    else 
      let cleans2 = clean (enot r) proof2 in
      if not (cleans2 = [])
      then
	let prf1 = lltolkrule (List.hd cleans2) [p] in
	let prf2 = lltolkrule proof1 [r] in
	sccut (p, prf1, prf2)
      else tryconstructive llproof r false
  | Rnoteq a, [], [] -> 
    righttoleft (eapp ("=", [a; a])) (sceqref (a, gamma))
  | Rnoteq a, [], [r] ->
    if equal r (eapp ("=", [a; a])) 
    then sceqref (a, gamma)
    else 
      scrweak (r, sclnot (
	eapp ("=", [a; a]), 
	sceqref (a, rm (enot r) gamma)))
  | Reqsym (a, b), [], [] ->
    righttoleft (eapp ("=", [b; a]))
      (sceqsym (a, b, gamma))
  | Reqsym (a, b), [], [r] ->
    if equal r (eapp ("=", [b; a])) 
    then sceqsym (a, b, gamma)
    else
      scrweak (r, sclnot (
	eapp ("=", [b; a]), 
	sceqsym (a, b, rm (enot r) gamma)))
  | Rnotnot p, [proof], [] ->
    let prf = lltolkrule proof [] in
    righttoleft (enot (p))
      (scrnot (p, prf))
  | Rnotnot p, [proof], [r] ->
    if equal r (enot p) 
    then 
      let prf = lltolkrule proof [] in
      scrnot (p, prf)
    else tryconstructive llproof r false
  | Rconnect (And, p, q), [proof], _ ->
    let prf = lltolkrule proof right in
    scland (p, q, prf)
  | Rconnect (Or, p, q), [proof1; proof2], _ ->
    let prf1 = lltolkrule proof1 right in
    let prf2 = lltolkrule proof2 right in
    sclor (p, q, prf1, prf2)
  | Rconnect (Imply, p, q), [proof1; proof2], [] ->
    let prf1 = lltolkrule proof1 [] in
    let prf2 = lltolkrule proof2 [] in
    make_imply p q prf1 prf2;
  | Rconnect (Imply, p, q), [proof1; proof2], [r] ->
    let cleans1 = clean (enot r) proof1 in
    if not (cleans1 = [])
    then 
      let prf1 = lltolkrule (List.hd cleans1) [p] in
      let prf2 = lltolkrule proof2 [r] in
      sclimply (p, q, prf1, prf2)
    else 
      let cleans2 = clean (enot r) proof2 in
      if not (cleans2 = [])
      then
	let prf1 = lltolkrule proof1 [r] in
	let prf2 = lltolkrule (List.hd cleans2) [] in
	make_imply p q prf1 prf2
      else tryconstructive llproof r false
  | Rnotconnect (And, p, q), [proof1; proof2], [] ->
    let prf1 = lltolkrule proof1 [] in
    let prf2 = lltolkrule proof2 [] in
    make_not_and_l p q prf1 prf2
  | Rnotconnect (And, p, q), [proof1; proof2], [r] ->
    if equal r (eand (p, q))
    then
      let prf1 = lltolkrule proof1 [p] in
      let prf2 = lltolkrule proof2 [q] in
      scrand (p, q, prf1, prf2)
    else 
      let cleans1 = clean (enot r) proof1 in
      if not (cleans1 = [])
      then 
	let prf1 = lltolkrule (List.hd cleans1) [] in
	let prf2 = lltolkrule proof2 [r] in
	make_not_and_r p q prf1 prf2
      else 
	let cleans2 = clean (enot r) proof2 in
	if not (cleans2 = [])
	then
	  let prf1 = lltolkrule proof1 [r] in
	  let prf2 = lltolkrule (List.hd cleans2) [] in
	  make_not_and_l p q prf1 prf2  
	else tryconstructive llproof r false
  | Rnotconnect (Or, p, q), [proof], [] ->
    let prf = lltolkrule proof [] in
    make_not_or p q prf
  | Rnotconnect (Or, p, q), [proof], [r] ->
    if equal r (eor (p, q))
    then 
      let cleans1 = clean (enot p) proof in
      if not (cleans1 = [])
      then 
	let prf = lltolkrule (List.hd cleans1) [q] in
	scrorr (p, q, prf)
      else 
	let cleans2 = clean (enot q) proof in
	if not (cleans2 = [])
	then
	  let prf = lltolkrule (List.hd cleans2) [p] in
	  scrorl (p, q, prf)
	else tryconstructive llproof r false
    else
      let prf = lltolkrule proof [r] in
      make_not_or p q prf
  | Rnotconnect (Imply, p, q), [proof], [] ->
    let prf = lltolkrule proof [] in
    make_not_imply1 p q prf
  | Rnotconnect (Imply, p, q), [proof], [r] ->
    if equal r (eimply (p, q))
    then
      let prf = lltolkrule proof [q] in
      scrimply (p, q, prf)
    else
      let cleans = clean p proof in
      if not (cleans = [])
      then
	let prf = lltolkrule (List.hd (clean p proof)) [r] in
	make_not_imply2 p q prf
      else tryconstructive llproof r false
  | Rex (ep, v), [proof], _ ->
    let prf = lltolkrule proof right in
    sclex (ep, v, prf)
  | Rall (ap, t), [proof], _ ->
    let prf = lltolkrule proof right in
    sclall (ap, t, prf)
  | Rnotex (Eex(x, _, p, _) as ep, t), [proof], [] ->
    let prf = lltolkrule proof [] in
    make_not_exists (substitute [(x, t)] p) ep t prf
  | Rnotex (Eex(x, _, p, _) as ep, t), [proof], [r] ->
    if equal r ep 
    then
      let prf = lltolkrule proof [substitute [(x, t)] p] in
      screx (ep, t, prf)
    else
      let prf = lltolkrule proof [r] in
      make_not_exists (substitute [(x, t)] p) ep t prf  
  | Rnotall (Eall(x, _, p, _) as ap, v), [proof], [] ->
    let prf = lltolkrule proof [substitute [(x, v)] p] in
    righttoleft ap (scrall (ap, v, prf))
  | Rnotall (Eall(x, _, p, _) as ap, v), [proof], [r] ->
    if equal r ap
    then
      let prf = lltolkrule proof [substitute [(x, v)] p] in
      scrall (ap, v, prf)
    else tryconstructive llproof r false
  | Rpnotp (Eapp (_, ts, _) as e1, 
	    Enot (Eapp (_, us, _) as e2, _)), proofs, [] ->
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let prfs = 
      List.map2 (fun p eq -> lltolkrule p [eq]) proofs eqs in
    righttoleft e2 (sceqpropbis (e1, e2, prfs, gamma))
  | Rpnotp (Eapp (_, ts, _) as e1, 
	    Enot (Eapp (_, us, _) as e2, _)), proofs, [r] ->
    if equal r e2
    then
      let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
      let prfs = 
	List.map2 (fun p eq -> lltolkrule p [eq]) proofs eqs in
      sceqpropbis (e1, e2, prfs, gamma)
    else tryconstructive llproof r false
  | Rnotequal (Eapp (_, ts, _) as e1,
	       (Eapp (_, us, _) as e2)), proofs, [] ->
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let prfs = 
      List.map2 (fun p eq -> lltolkrule p [eq]) proofs eqs in
    righttoleft (eapp ("=", [e1; e2])) 
      (sceqfuncbis (e1, e2, prfs, gamma))
  | Rnotequal (Eapp (_, ts, _) as e1,
	       (Eapp (_, us, _) as e2)), proofs, [r] ->
    if equal r (eapp ("=", [e1; e2]))
    then
      let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
      let prfs = 
	List.map2 (fun p eq -> lltolkrule p [eq]) proofs eqs in
      sceqfuncbis (e1, e2, prfs, gamma)
    else tryconstructive llproof r false
  | Rextension ("", "zenon_stringequal", [s1; s2], [c], _), _, _ ->
    let v1 = eapp ("$string", [s1]) in
    let v2 = eapp ("$string", [s2]) in
    let n1 = List.assoc v1 !distinct_terms in
    let n2 = List.assoc v2 !distinct_terms in
    let context = List.fold_left (fun l e -> rm e l) gamma right in
    let prf = 
      if n1 < n2
      then righttoleft c (scaxiom (c, rm (enot c) context))
      else righttoleft c (sceqsym (v1, v2, rm (enot c) context)) in
    List.fold_left (fun prf e -> scrweak (e, prf)) prf right
  | Rextension ("", s, [e1; v1; e2; v2], [c1; c2], _), [proof], _ ->
    let prf = lltolkrule proof right in
    let context = List.fold_left (fun l e -> rm e l) gamma right in
    let b1, b2 = match s with
      | "zenon_stringdiffll" -> true, true
      | "zenon_stringdifflr" -> true, false
      | "zenon_stringdiffrl" -> false, true
      | "zenon_stringdiffrr" -> false, false 
      | _ -> assert false in
    deduce_inequality e1 e2 v1 v2 c1 c2 b1 b2 context prf
  | RcongruenceLR _, _, _
  | RcongruenceRL _, _, _
  | Rdefinition _, _, _
  | Rextension _, _, _ 
  | Rlemma _, _, _ 
  | Rconnect (Equiv, _, _), _, _ 
  | Rnotconnect (Equiv, _, _), _, _ ->
    assert false
  | _ -> assert false

and lltolkrule proof right =
  let translate prf =
    (*p_debug_lkproof "proof" prf;*)
    List.fold_left
      (fun prf c -> sclcontr (c, prf))
      prf proof.ccontr
  in match right with
  | [r] ->
    begin match clean (enot r) proof with
    | cproof :: cproofs ->
      if inlist (enot r) proof.ccontr
      then lltolkrule cproof [r]
      else
	let prf = lltolkrule cproof [] in
	scrweak (r, prf)
    | [] ->
      if inlist (enot r) proof.ccontr &&
	oneinlist (enot r) proof.cgamma
      then
	begin
	  match r with
	  | Enot _ -> assert false
	  | _ ->
	    tryconstructive proof r true
	end
      else translate (xlltolkrule proof right) end
  | _ -> translate (xlltolkrule proof right)
;;

let rec lltolk proof goal =
  let newproof = use_defs_proof proof in
  let right, newgoal, newgamma =
    match goal with
    | Some (Enot (g, _)) -> 
      let ng = use_defs g in
      [ng], ng, (enot ng) :: List.map use_defs !hypothesis_env
    | None -> [], efalse, List.map use_defs !hypothesis_env
    | _ -> assert false in
  let l, newproof = addcontrs newproof newgamma in
  assert (l = []);
  (*p_debug_llproof "prf" newproof;*)
  let lkproof = lltolkrule newproof right in
  newgoal, lkproof
;;
      
(*--------------------------------------------------------*)

let rec newcut l aplus proof1 proof2 = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  if equal aplus c1 
  then
    l, sccut (aplus, proof1, proof2)
  else 
    match c1 with
    | Enot (Enot (c, _), _) when equal c aplus ->
      if equal c2 efalse
      then 
	l, sccut (
	  c1, proof1, 
	  sclnot (enot c, scrnot (c, proof2)))
      else
	l, sccut (
	  c1, proof1, 
	  scrnot (
	    enot c2, sclnot (
	      enot c, scrnot (
		c, sclnot (c2, proof2)))))
    | _ -> 
      p_debug "\nfail cut" [c1; aplus];
      assert false
;;
	
let rec weaken ex et = 
  match ex, et with
  | Enot (Enot (fx, _), _), Enot (Enot (ft, _), _) -> 
    enot (enot (weaken fx ft))
  | _, Enot (Enot (ft, _), _) -> enot (enot (weaken ex ft))
  | Etrue, _ | Efalse, _
  | Evar _, _ | Eapp _, _-> ex
  | Eand (fx1, fx2, _), Eand (ft1, ft2, _) -> 
    eand (weaken fx1 ft1, weaken fx2 ft2)
  | Eor (fx1, fx2, _), Eor (ft1, ft2, _) -> 
    eor (weaken fx1 ft1, weaken fx2 ft2)
  | Eimply (fx1, fx2, _), Eimply (ft1, ft2, _) -> 
    eimply (weaken fx1 ft1, weaken fx2 ft2)
  | Enot (fx, _), Enot (ft, _) -> enot (weaken fx ft)
  | Eall (x, tyx, fx, _), Eall (y, _, ft, _) ->
    eall (x, tyx, weaken fx (substitute [(y, x)] ft))
  | Eex (x, tyx, fx, _), Eex (y, _, ft, _) ->
    eex (x, tyx, weaken fx (substitute [(y, x)] ft))
  | _, _ -> assert false
;;

let rec unify e1 e2 =
  match e1, e2 with
  | Enot (Enot (f1, _), _), Enot (Enot (f2, _), _) -> 
    enot (enot (unify f1 f2))
  | Enot (Enot (f1, _), _), _ -> enot (enot (unify f1 e2))
  | _, Enot (Enot (f2, _), _) -> enot (enot (unify e1 f2))
  | Etrue, Etrue -> etrue
  | Efalse, Efalse -> efalse
  | Evar (x, _), Evar (y, _) when (x = y) -> evar (x)
  | Eapp (x, args1, _), Eapp (y, args2, _) 
    when (x = y && List.for_all2 equal args1 args2) -> 
    eapp (x, args1)
  | Eand (f1, f2, _), Eand (f3, f4, _) -> 
    eand (unify f1 f3, unify f2 f4)
  | Eor (f1, f2, _), Eor (f3, f4, _) -> 
    eor (unify f1 f3, unify f2 f4)
  | Eimply (f1, f2, _), Eimply (f3, f4, _) -> 
    eimply (unify f1 f3, unify f2 f4)
  | Enot (f1, _), Enot (f2, _) -> enot (unify f1 f2)
  | Eall (x, ty1, f1, _), Eall (y, _, f2, _) ->
    eall (x, ty1, unify f1 (substitute [(y, x)] f2))
  | Eex (x, ty1, f1, _), Eex (y, _, f2, _) ->
    eex (x, ty1, unify f1 (substitute [(y, x)] f2))
  | _, _ -> p_debug "fail unify" [e1; e2]; assert false
;;

let rec merge l1 l2 = 
  let ll,l = List.fold_left 
    (fun (q, r) (a, b) ->
      let c = List.assoc a q in
      List.remove_assoc a q, (a, c, b, unify b c) :: r)
    (l1, []) l2 in 
  assert (ll = []);
  l
;;

let rec adaptaxiom g e1 e2 =
  match e1, e2 with
  | Etrue, Etrue | Efalse, Efalse
  | Evar _, Evar _ | Eapp _, Eapp _ 
    -> scaxiom (e1, g)
  | Enot (f1, _), Enot (f2, _) -> 
    scrnot (
      f2, sclnot (
	f1, adaptaxiom g f2 f1))
  | Eand (f1, f2, _), Eand (f3, f4, _) -> 
    scland (f1, f2, scrand (
      f3, f4, 
      adaptaxiom (f2 :: g) f1 f3,
      adaptaxiom (f1 :: g) f2 f4))
  | Eor (f1, f2, _), Eor (f3, f4, _) -> 
    sclor (
      f1, f2, 
      scrorl (f3, f4, adaptaxiom g f1 f3),
      scrorr (f3, f4, adaptaxiom g f2 f4))
  | Eimply (f1, f2, _), Eimply (f3, f4, _) -> 
   scrimply (f3, f4, sclimply (
     f1, f2,
     adaptaxiom g f3 f1, 
     adaptaxiom (f3 :: g) f2 f4))
  | Eall (x, ty, f1, _), Eall (y, _, f2, _) ->
    let z = new_var () in
    scrall (
      e2, z, sclall (
	e1, z, adaptaxiom g 
	  (substitute [(x, z)] f1) 
	  (substitute [(y, z)] f2)))
  | Eex (x, ty, f1, _), Eex (y, _, f2, _) ->
    let z = new_var () in
    sclex (
      e1, z, screx (
	e2, z, adaptaxiom g
	  (substitute [(x, z)] f1) 
	  (substitute [(y, z)] f2)))
  | _, Enot (Enot (f2, _), _) ->
    scrnot (
      enot (f2), sclnot (
	f2, adaptaxiom g e1 f2))
  | _, _ -> assert false   
;;

let rec ladapt proof (u, v) =
  (*p_debug "ladapt" [u; v];*)
  if equal u v then proof else
    let g, c, rule = proof in
    let result = match rule, v with
    | SClor (a, b, proof1, proof2), Eor (sa, sb, _) 
      when (equal u (eor (a, b))) -> 
      sclor (sa, sb, ladapt proof1 (a, sa), ladapt proof2 (b, sb))
    | SClimply (a, b, proof1, proof2), Eimply (sa, sb, _)
      when (equal u (eimply (a, b))) ->
      sclimply (
	sa, sb, radapt proof1 (a, sa), ladapt proof2 (b, sb))
    | SClcontr (a, proof), _ 
      when (equal a u) ->
      sclcontr (v, ladapt (ladapt proof (a, v)) (a, v))
    | SCland (a, b, proof), Eand (sa, sb, _) 
      when (equal u (eand (a, b))) ->
      scland (sa, sb, ladapt (ladapt proof (a, sa)) (b, sb))
    | SClnot (a, proof), Enot (sa, _) 
      when (equal u (enot a)) ->
      sclnot (sa, radapt proof (a, sa))
    | SClall (Eall (var, ty, e, _) as ap, t, proof), 
	Eall (svar, _, se, _) 
	  when (equal u ap) ->
      let z = substitute [(var, t)] e in
      let sz = substitute [(svar, t)] se in
      sclall (eall (svar, ty, se), t, ladapt proof (z, sz))
    | SClex (Eex (var, ty, e, _) as ep, v, proof), 
      Eex (svar, _, se, _) 
	when (equal u ep) ->
      let z = substitute [(var, v)] e in
      let sz = substitute [(svar, v)] se in
      sclex (eex (svar, ty, se), v, ladapt proof (z, sz))
    | _, _ -> 
      match rule with
      | SCaxiom a when equal u a -> 
	(*assert (inlist u g);*)
	adaptaxiom (rm u g) v u
      | SClnot _ | SClimply _ | SClor _ | SCland _
      | SClcontr _ | SCcut _ | SClex _ | SClall _ 
      | SCrweak _ | SCrnot _ | SCrand _ | SCrimply _ 
      | SCrorl _ | SCrorr _ | SCrall _ | SCrex _
	-> applytohyps (fun proof -> ladapt proof (u, v)) proof    
      | SCeqfunc _ | SCeqprop _ | SCaxiom _ | SCfalse | SCtrue 
      | SCeqref _ | SCeqsym _ -> v :: (rm u g), c, rule
      | SCcnot _ -> assert false in 
    (*let resultg, _, _ = result in
    assert (List.length resultg = List.length g);*)
    result

and radapt proof (a, b) =
  (*p_debug "radapt" [a; b];*)
  let rec xadapt proof (u, v) =
    let g, c, rule = proof in
    match rule, v with
    | SCcut (a, proof1, proof2), _ -> 
      sccut (a, proof1, radapt proof2 (u, v))
    | SClimply (a, b, proof1, proof2), _ ->
      sclimply (a, b, proof1, radapt proof2 (u, v)) 
    | SCrand (a, b, proof1, proof2), Eand (xa, xb, _) ->
      scrand (xa, xb, radapt proof1 (a, xa), radapt proof2 (b, xb))
    | SCrweak (a, proof), _ -> scrweak (v, proof)
    | SClnot (a, proof), _ -> sclnot (a, proof)
    | SCrorl (a, b, proof), Eor (xa, xb, _) ->
      scrorl (xa, xb, radapt proof (a, xa))
    | SCrorr (a, b, proof), Eor (xa, xb, _) ->
      scrorr (xa, xb, radapt proof (b, xb))
    | SCrimply (a, b, proof), Eimply (xa, xb, _) ->
      scrimply (xa, xb, radapt (ladapt proof (a, xa)) (b, xb))
    | SCrnot (a, proof), Enot (xa, _) ->
      scrnot (xa, ladapt proof (a, xa))
    | SCrall (Eall (var, ty, e, _), v, proof),
      Eall (xvar, _, xe, _) ->
      let z = substitute [(var, v)] e in
      let xz = substitute [(xvar, v)] xe in  
      scrall (eall (xvar, ty, xe), v, radapt proof (z, xz))
    | SCrex (Eex (var, ty, e, _), t, proof),
      Eex (xvar, _, xe, _) ->
      let z = substitute [(var, t)] e in
      let xz = substitute [(xvar, t)] xe in  
      screx (eex (xvar, ty, xe), t, radapt proof (z, xz))
    | _, _ -> match rule with
      | SCtrue | SCeqref _ | SCeqsym _ 
      | SCeqfunc _ | SCeqprop _  -> proof
      | SCaxiom _ -> adaptaxiom (rm u g) u v
      | SCfalse -> g, v, rule
      | SClcontr _ | SClor _ | SCland _ | SClall _ | SClex _
	-> applytohyps (fun proof -> radapt proof (u, v)) proof 
      | SCcnot _ -> assert false
      | _ -> p_debug "u, v fail" [u; v];
	assert false in
  let rec headnots e1 e2 =
    match e1, e2 with
    | Enot (Enot (f1, _), _), Enot (Enot (f2, _), _) -> 
      headnots f1 f2
    | _, Enot (Enot (f2, _), _) -> true
    | _, _ -> false in
  if equal a b 
  then proof 
  else
    if headnots a b 
    then 
      match b with
      | Enot (Enot (e, _), _) -> 
	scrnot (enot (e), sclnot (e, radapt proof (a, e)))
      | _ -> assert false;
    else
      xadapt proof (a, b)
;;

let rec lltoljrule lkproof =
  (*p_debug_proof "\nseq" lkproof;*)
  let replace1 list = 
    List.map (fun (a, b, c, d) -> (b, d)) list in
  let replace2 list = 
    List.map (fun (a, b, c, d) -> (c, d)) list in
  let replace3 list =
    List.map (fun (a, b, c, d) -> (a, d)) list in
  let lkg, lkc, rule = lkproof in
  let assocs, proofs =
    List.split (List.map lltoljrule (hypsofrule rule)) in
  let ljlist, ljprf =
  match rule, assocs, proofs with
    | SCcut (a, lklkprf1, lklkprf2), [l1; l2],
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge l1 (List.remove_assoc a l2) in
      let q1 = replace1 l in
      let q2 = replace2 l in
      newcut (replace3 l) (List.assoc a l2)
	(List.fold_left ladapt proof1 q1)
	(List.fold_left ladapt proof2 q2)
    | SClor (a, b, _, _), [l1; l2], 
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = 
	merge (List.remove_assoc a l1) (List.remove_assoc b l2) in
      let q1 = replace1 l in
      let q2 = replace2 l in
      let c3 = unify c1 c2 in
      (eor (a, b), eor (List.assoc a l1, List.assoc b l2)) :: (replace3 l),
      sclor (
	List.assoc a l1, List.assoc b l2, 
	radapt (List.fold_left ladapt proof1 q1) (c1, c3), 
	radapt (List.fold_left ladapt proof2 q2) (c2, c3))
    | SClimply (a, b, _, _), [l1; l2], 
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge l1 (List.remove_assoc b l2) in
      (*assert (List.for_all morenotsinright l1);*)
      (*assert (List.for_all morenotsinright l2);*)
      let b2 = List.assoc b l2 in
      let q1 = replace1 l in
      (*assert (List.for_all morenotsinright q1);*)
      let q2 = replace2 l in
      (*assert (List.for_all morenotsinright q2);*)
      (eimply (a, b), eimply (c1, List.assoc b l2)) :: (replace3 l),
      sclimply (
	c1, b2, 
	List.fold_left ladapt proof1 q1, 
	List.fold_left ladapt proof2 q2)
    | SCrand (a, b, _, _), [l1; l2], 
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge l1 l2 in
      let q1 = replace1 l in
      let q2 = replace2 l in
      (replace3 l), scrand (
	c1, c2, 
	List.fold_left ladapt proof1 q1, 
	List.fold_left ladapt proof2 q2)
    | SClcontr (a, _), [l], [(g, c, _) as proof] ->
      (*eprintf "\nproblem with contraction\n";*)   
      let a1 = List.assoc a l in
      let a2 = List.assoc a (List.remove_assoc a l) in
      let a3 = unify 
	(List.assoc a l) 
	(List.assoc a (List.remove_assoc a l)) in
      (*p_debug "erfvrefv" [a1; a2; a3];
      let prooof = (ladapt proof (a2, a3)) in
      eprintf "\nproblem with contraction\n";*)
      (a, a3)
      :: List.remove_assoc a (List.remove_assoc a l),
      sclcontr (a3, ladapt (ladapt proof (a1, a3)) (a2, a3))
    | SCaxiom _, _, _ | SCfalse, _, _
    | SCtrue, _, _ | SCeqref _, _, _ | SCeqsym _, _, _
    | SCeqfunc _, _, _
      -> List.map (fun x -> (x, x)) lkg, lkproof
    | SCeqprop _, _ , _
      -> 
	List.map (fun x -> (x, x)) lkg, lkproof
    | SCrweak (a, _), [l], [(g, c, _) as proof] -> 
      l, scrweak (a, proof)
    | SCland (a, b, _), [l], [(g, c, _) as proof] ->
      (eand (a, b), eand (List.assoc a l,List.assoc b l))
      :: (List.remove_assoc a (List.remove_assoc b l)),
      scland (List.assoc a l, List.assoc b l, proof)
    | SClnot (e, _), [l], [(g, c, _) as proof] ->
      (enot e, enot c) :: l, sclnot (c, proof)
    | SCrorl (a, b, _), [l], [(g, c, _) as proof] ->
      l, scrorl (c, b, proof)
    | SCrorr (a, b, _), [l], [(g, c, _) as proof] ->
      l, scrorr (a, c, proof)
    | SCrimply (a, b, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc a l, scrimply (List.assoc a l, c, proof)
    | SCrnot (a, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc a l,
      scrnot (List.assoc a l, proof) 
    | SClall (Eall (x, ty, e, _) as ap, t, _), 
      [l], [(g, c, _) as proof] ->
      let f = use_defs (substitute [(x, t)] e) in
      let h = eall (
	x, ty, 
	weaken e (List.assoc f l)) in
      (ap, h) :: (List.remove_assoc f l),
      sclall (h, t, proof)
    | SClex (Eex (x, ty, e, _) as ep, v, _), 
      [l], [(g, c, _) as proof] ->
      let f = use_defs (substitute [(x, v)] e) in
      let h = eex (
	x, ty, 
	weaken e (List.assoc f l)) in
      (ep, h) :: (List.remove_assoc f l),
      sclex (h, v, proof)
    | SCrall (Eall (x, ty, e, _), v, _), [l], 
      [(g, c, _) as proof] ->
      l, scrall (eall (x, ty, weaken e c), v, proof)
    | SCrex (Eex (x, ty, e, _), t, _), [l], [(g, c, _) as proof] ->
      l, screx (eex (x, ty, weaken e c), t, proof)
    | SCcnot (e, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc (enot e) l, 
      scrnot (List.assoc (enot e) l, proof)
    | _, _, _ -> assert false in
  (*let ljg, _, _ = ljprf in
  assert (List.length lkg = List.length ljg);*)
  (*assert (List.length ljlist = List.length ljg);*)
  (*assert (List.for_all morenotsinright ljlist);*)
  (*p_debug_proof "\nresult" ljprf;*)
  ljlist, ljprf

and morenotsinright (a, b) =
  match a, b with
  | Enot (Enot (fx, _), _), Enot (Enot (ft, _), _) -> 
    morenotsinright (fx, ft)
  | _, Enot (Enot (ft, _), _) -> 
    morenotsinright (a, ft)
  | Etrue, _ | Efalse, _
  | Evar _, _ | Eapp _, _-> true
  | Eand (fx1, fx2, _), Eand (ft1, ft2, _) 
  | Eor (fx1, fx2, _), Eor (ft1, ft2, _) 
  | Eimply (fx1, fx2, _), Eimply (ft1, ft2, _) -> 
    morenotsinright (fx1, ft1) &&  morenotsinright (fx2, ft2)
  | Enot (fx, _), Enot (ft, _) -> 
    morenotsinright (fx, ft)
  | Eall (x, _, fx, _), Eall (y, _, ft, _) ->
    morenotsinright (fx, ft)
  | Eex (x, _, fx, _), Eex (y, _, ft, _) ->
    morenotsinright (fx, ft)
  | _, _ -> false
;;

let rec lltolj proof goal =
  let result = lltolk proof goal in
  let conc, lkproof = List.fold_left
    (fun (conc, rule) stmt ->
      let newstmt = use_defs stmt in
      eimply (newstmt, conc), 
      scrimply (newstmt, conc, rule)
    )
    result !hypothesis_env in
  (*p_debug_lkproof "lkproof" lkproof;*)
  let _, ljproof = lltoljrule (*optimize lkproof*)lkproof in
  ljproof
;;


(*open Printf;;
open Expr;;
open Llproof;;
open Namespace;;

let new_var = 
  let r = ref 0 in
  fun () -> 
    let n = !r in
    incr r;
    evar (sprintf "v%d" n)
;;

exception Found of expr;;

let p_debug s es = 
  eprintf "%s |" s;
  List.iter
    (eprintf " %a |" 
       (fun oc x -> Print.expr (Print.Chan oc) x)
    ) es; 
  eprintf "\n";
;;

let p_debug_proof s (g, c, rule) =
  eprintf "%s : gamma = |" s;
  List.iter
    (eprintf " %a |" 
       (fun oc x -> Print.expr (Print.Chan oc) x)) g; 
  eprintf "\n and conc = |";
  eprintf " %a |" 
    (fun oc x -> Print.expr (Print.Chan oc) x) c;
  eprintf "\n";
;;

type sequent = expr list * expr list

type tree = {
  conclusion : expr list;
  gamma : expr list;
  newrule : rule; 
  newhyps : tree list; 
  contracted : expr list;
};; 

type lkrule =
| SCaxiom of expr
| SCfalse
| SCtrue
| SCeqref of expr
| SCeqsym of expr * expr
| SCeqprop of expr * expr
| SCeqfunc of expr * expr
| SCrweak of expr * lkproof
| SClcontr of expr * lkproof
| SCcut of expr * lkproof * lkproof
| SCland of expr * expr * lkproof
| SClor of expr * expr * lkproof * lkproof
| SClimply of expr * expr * lkproof * lkproof
| SClnot of expr * lkproof
| SClall of expr * expr * lkproof
| SClex of expr * expr * lkproof
| SCrand of expr * expr * lkproof * lkproof
| SCrorl of expr * expr * lkproof
| SCrorr of expr * expr * lkproof
| SCrimply of expr * expr * lkproof
| SCrnot of expr * lkproof
| SCrall of expr * expr * lkproof
| SCrex of expr * expr * lkproof
| SCcnot of expr * lkproof

and lkproof = 
  expr list * expr * lkrule
;;

let ingamma e proof =
  let g, c, rule = proof in
  List.exists (equal e) g
;;

let rec rm a list =
  match list with
  | x :: list when equal x a -> list
  | x :: list -> x :: (rm a list)
  | [] -> assert false
;;

let scaxiom (e, g) = e :: g, e, SCaxiom e;;
let scfalse (g, e) = efalse :: g, e, SCfalse;;
let sctrue (g) = g, etrue, SCtrue;;
let sceqref (a, g) = g, eapp ("=", [a; a]), SCeqref (a);;
let sceqsym (a, b, g) =
  eapp ("=", [a; b]) :: g, eapp ("=", [b; a]), SCeqsym (a, b);;
let sceqprop (e1, e2, g) =
  match e1, e2 with
  | Eapp (p, ts, _), Eapp (q, us, _) when p = q ->
    e1 :: g @ List.map2 (fun t u -> eapp ("=", [t; u])) ts us, e2, 
    SCeqprop (e1, e2)
  | _, _ -> assert false
let sceqfunc (e1, e2, g) =
  match e1, e2 with
  | Eapp (p, ts, _), Eapp (q, us, _) when p = q ->
    g @ List.map2 (fun t u -> eapp ("=", [t; u])) ts us, 
    eapp ("=", [e1; e2]), SCeqfunc (e1, e2)
  | _, _ -> assert false
let scrweak (e, proof) =
  let g, c, rule = proof in
  (*p_debug_proof "fail with sequent" proof*)
  assert (equal c efalse);
  if (equal e efalse)
  then proof
  else g, e, SCrweak (e, proof);;
let sclcontr (e, proof) =
  let g, c, rule = proof in
  (*p_debug "\n contract element" [e];
  p_debug_proof "\n in list" proof;*)
  assert (inlist e g);
  assert (inlist e (rm e g));
  rm e g, c, SClcontr (e, proof)
let sccut (e, proof1, proof2) = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  (*p_debug "\nsccut" [e];
  p_debug_proof "of proof1" proof1;
  p_debug_proof "and proof2" proof2;*)
  assert (List.length g2 = List.length g1 + 1);
  assert (equal c1 e);
  g1, c2, SCcut(e, proof1, proof2);;
let scland (e1, e2, proof) = 
  assert (ingamma e2 proof);
  let (g, c, rule) = proof in
  assert (inlist e1 (rm e2 g));
  (eand (e1, e2)) :: rm e1 (rm e2 g), c, SCland (e1, e2, proof);;
let sclor (e1, e2, proof1, proof2) = 
  assert (ingamma e1 proof1);
  let (g1, c, rule1) = proof1 in
  let (g2, _, _) = proof2 in
  assert (List.length g2 = List.length g1);
  (eor (e1, e2)) :: rm e1 g1, c, SClor (e1, e2, proof1, proof2);;
let sclimply (e1, e2, proof1, proof2) = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  assert (List.length g2 = List.length g1 + 1);
  (eimply (e1, e2)) :: g1, c2, 
  SClimply (e1, e2, proof1, proof2);;
let sclnot (e, proof) = 
  let (g, d, rule) = proof in
  assert (equal e d);
  (enot e) :: g, efalse, SClnot (e, proof);;
let sclall (e1, t, proof) = 
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, c, rule) = proof in
    assert (ingamma (substitute [(x, t)] p) proof);
    e1 :: rm (substitute [(x, t)] p) g, c, SClall (e1, t, proof)
  | _ -> assert false;;
let sclex (e1, v, proof) = 
  match e1 with
  | Eex (x, ty, p, _) ->
    let (g, c, rule) = proof in
    assert (ingamma (substitute [(x, v)] p) proof);
    e1 :: rm (substitute [(x, v)] p) g, c, SClex (e1, v, proof)
  | _ -> assert false;;
let scrand (e1, e2, proof1, proof2) = 
  let (g1, d1, rule1) = proof1 in
  let (g2, _, _) = proof2 in
  assert (List.length g2 = List.length g1);
  g1, eand (e1, e2), SCrand (e1, e2, proof1, proof2);;
let scrorl (e1, e2, proof) = 
  let (g, d, rule) = proof in
  g, eor (e1, e2), SCrorl (e1, e2, proof);;
let scrorr (e1, e2, proof) = 
  let (g, d, rule) = proof in
  g, eor (e1, e2), SCrorr (e1, e2, proof);;
let scrimply (e1, e2, proof) = 
  assert (ingamma e1 proof);
  let (g, d, rule) = proof in
  rm e1 g, eimply (e1, e2), SCrimply (e1, e2, proof);;
let scrnot (e, proof) = 
  assert (ingamma e proof);
  let (g, d, rule) = proof in
  rm e g, enot e, SCrnot (e, proof);;
let scrall (e1, v, proof) = 
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, c, rule) = proof in
    g, e1, SCrall (e1, v, proof)
  | _ -> assert false;;
let screx (e1, t, proof) = 
  match e1 with
  | Eex (x, ty, p, _) ->
    let (g, c, rule) = proof in
    g, e1, SCrex (e1, t, proof)
  | _ -> assert false;;
(*let sclnotnot (e, proof) = 
  let (g, c, rule) = proof in
  assert (inlist (enot (enot e)) g);
  e :: (rm (enot (enot e)) g), c, SClnotnot (e, proof);;
let scrnotnot (e, proof) = 
  let (g, c, rule) = proof in
  assert (equal (enot (enot e)) c);
  g, e, SCrnotnot (e, proof);;*)
let sccnot (e, proof) = 
  let (g, c, rule) = proof in
  assert (equal c efalse);
  assert (inlist (enot e) g);
  rm (enot e) g, e, SCcnot (e, proof);;
let scconc (g, c, rule) = c;;

let lemma_env = 
  (Hashtbl.create 97 : (string, prooftree) Hashtbl.t)
;;

let distinct_terms = ref [];;

let hypothesis_env = ref [];;

let definition_env =
  (Hashtbl.create 97 : (string, expr list * expr) Hashtbl.t)
;;

let rew_env = ref ((Hashtbl.create 97 : (string, expr * expr) Hashtbl.t),
		   (Hashtbl.create 97 : (string, expr * expr) Hashtbl.t));;

let new_terms = ref [];;

let gamma_length (g, c, rule) = List.length g;;

let hypsofrule lkrule =
  match lkrule with
  | SCaxiom (e) -> []
  | SCfalse -> []
  | SCtrue -> []
  | SCeqref (e) -> []
  | SCeqsym (e1, e2) -> []
  | SCeqprop (e1, e2) -> []
  | SCeqfunc (e1, e2) -> []
  | SCrweak (e, proof) -> [proof]
  | SClcontr (e, proof) -> [proof]
  | SCcut (e, proof1, proof2) -> [proof1; proof2]
  | SCland (e1, e2, proof) -> [proof]
  | SClor (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClimply (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClnot (e, proof) -> [proof]
  | SClall (e1, e2, proof) -> [proof]
  | SClex (e1, e2, proof) -> [proof]
  | SCrand (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SCrorl (e1, e2, proof) -> [proof]
  | SCrorr (e1, e2, proof) -> [proof]
  | SCrimply (e1, e2, proof) -> [proof]
  | SCrnot (e, proof) -> [proof]
  | SCrall (e1, e2, proof) -> [proof]
  | SCrex (e1, e2, proof) -> [proof]
  | SCcnot (e, proof) -> [proof]
;;

let applytohyps f lkproof =
  let g, c, lkrule = lkproof in
  match lkrule with
  | SCaxiom (e) -> g, c, SCaxiom (e)
  | SCfalse -> g, c, SCfalse
  | SCtrue -> g, c, SCtrue
  | SCeqref (e) -> g, c, SCeqref (e)
  | SCeqsym (e1, e2) -> g, c, SCeqsym (e1, e2)
  | SCeqprop (e1, e2) -> g, c, SCeqprop (e1, e2)
  | SCeqfunc (e1, e2) -> g, c, SCeqfunc (e1, e2)
  | SCrweak (e, proof) -> scrweak (e, f proof)
  | SClcontr (e, proof) -> sclcontr (e, f proof)
  | SCcut (e, proof1, proof2) ->
    sccut (e, f proof1, f proof2)
  | SCland (e1, e2, proof) ->
    scland (e1, e2, f proof)
  | SClor (e1, e2, proof1, proof2) ->
    sclor (e1, e2, f proof1, f proof2)
  | SClimply (e1, e2, proof1, proof2) ->
    sclimply (e1, e2, f proof1, f proof2)
  | SClnot (e, proof) -> sclnot (e, f proof)
  | SClall (e1, e2, proof) -> sclall (e1, e2, f proof)
  | SClex (e1, e2, proof) -> sclex (e1, e2, f proof)
  | SCrand (e1, e2, proof1, proof2) ->
    scrand (e1, e2, f proof1, f proof2)
  | SCrorl (e1, e2, proof) -> 
    scrorl (e1, e2, f proof)
  | SCrorr (e1, e2, proof) ->
    scrorr (e1, e2, f proof)
  | SCrimply (e1, e2, proof) ->
    scrimply (e1, e2, f proof)
  | SCrnot (e, proof) -> scrnot (e, f proof)
  | SCrall (e1, e2, proof) -> scrall (e1, e2, f proof)
  | SCrex (e1, e2, proof) -> screx (e1, e2, f proof)
  | SCcnot (e, proof) -> sccnot (e, f proof)
;;

let applytohyps2 fs lkproof =
  let g, c, lkrule = lkproof in
  match lkrule, fs with
  | SCaxiom (e), [] -> g, c, SCaxiom (e)
  | SCfalse, [] -> g, c, SCfalse
  | SCtrue, [] -> g, c, SCtrue
  | SCeqref (e), [] -> g, c, SCeqref (e)
  | SCeqsym (e1, e2), [] -> g, c, SCeqsym (e1, e2)
  | SCeqprop (e1, e2), [] -> g, c, SCeqprop (e1, e2)
  | SCeqfunc (e1, e2), [] -> g, c, SCeqfunc (e1, e2)
  | SCrweak (e, proof), [f] -> scrweak (e, f proof)
  | SClcontr (e, proof), [f] -> sclcontr (e, f proof)
  | SCcut (e, proof1, proof2), [f1; f2] ->
    sccut (e, f1 proof1, f2 proof2)
  | SCland (e1, e2, proof), [f] ->
    scland (e1, e2, f proof)
  | SClor (e1, e2, proof1, proof2), [f1; f2] ->
    sclor (e1, e2, f1 proof1, f2 proof2)
  | SClimply (e1, e2, proof1, proof2), [f1; f2] ->
    sclimply (e1, e2, f1 proof1, f2 proof2)
  | SClnot (e, proof), [f] -> sclnot (e, f proof)
  | SClall (e1, e2, proof), [f] -> sclall (e1, e2, f proof)
  | SClex (e1, e2, proof), [f] -> sclex (e1, e2, f proof)
  | SCrand (e1, e2, proof1, proof2), [f1; f2] ->
    scrand (e1, e2, f1 proof1, f2 proof2)
  | SCrorl (e1, e2, proof), [f] -> 
    scrorl (e1, e2, f proof)
  | SCrorr (e1, e2, proof), [f] ->
    scrorr (e1, e2, f proof)
  | SCrimply (e1, e2, proof), [f] ->
    scrimply (e1, e2, f proof)
  | SCrnot (e, proof), [f] -> scrnot (e, f proof)
  | SCrall (e1, e2, proof), [f] -> scrall (e1, e2, f proof)
  | SCrex (e1, e2, proof), [f] -> screx (e1, e2, f proof)
  | SCcnot (e, proof), [f] -> sccnot (e, f proof)
  | _, _ -> assert false
;;

let rec xaddhyp h lkproof =
  let g, c, lkrule = lkproof in 
  match lkrule with
  | SCaxiom _ | SCfalse 
  | SCtrue | SCeqref _ | SCeqsym _ 
  | SCeqprop _ | SCeqfunc _ -> 
    h :: g, c, lkrule
  | _ -> applytohyps (xaddhyp h) lkproof
    
and addhyp hyps lkproof =
  List.fold_left (fun pf h -> xaddhyp h pf) lkproof hyps
;;  

let sceqpropbis (e1, e2, proofs, gamma) = 
  (*List.iter (fun proof ->
    p_debug "\ngamma" gamma;
    p_debug_proof "proof" proof;
    assert (List.length gamma = gamma_length proof)) proofs;*)
  match e1, e2 with
  | Eapp (_, ts, _), Eapp (_, us, _) ->
    let prf0 = sceqprop (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2 
	(fun (l, prf) eq proof ->
	  assert (inlist eq l);
	  let hyps = rm eq l in
	  assert (gamma_length prf = 
	     gamma_length (addhyp hyps proof) + 1);
	  hyps, sccut (eq, addhyp hyps proof, prf))
	(e1 :: eqs, prf0) eqs proofs in
    proof
  | _, _ -> assert false
;;
let sceqfuncbis (e1, e2, proofs, gamma) =
  match e1, e2 with
  | Eapp (_, ts, _), Eapp (_, us, _) ->
    let prf0 = sceqfunc (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2 
	(fun (l, prf) eq proof ->
	  assert (inlist eq l);
	  let hyps = rm eq l in
	  assert (gamma_length prf = 
	     gamma_length (addhyp hyps proof) + 1);
	  hyps, sccut (eq, addhyp hyps proof, prf))
	(eqs, prf0) eqs proofs in
    proof
  | _, _ -> assert false
;;

let rec oneinlist a l =
  match l with
  | [] -> false
  | x :: q when (equal x a) ->
    not (inlist a q)
  | x :: q -> oneinlist a q
;;

let rec use_defs expression = 
  let e = List.hd (Rewrite.normalize_fm (!rew_env) expression) in
(*  let e = List.hd [expression] in *)
  match e with
  | Evar (v, _) when Hashtbl.mem definition_env v -> 
    let (params, body) = Hashtbl.find definition_env v in
    body
  | Eapp (s, args, _) when Hashtbl.mem definition_env s ->
    let exprs = List.map use_defs args in
    let (params, body) = Hashtbl.find definition_env s in
    substitute (List.combine params exprs) body
  | Evar _ | Etrue | Efalse -> e
  | Eapp (s, args, _) ->
    eapp (s, List.map use_defs args)
  | Enot (e, _) ->
    enot (use_defs e)
  | Eand (e1, e2, _) ->
    eand (use_defs e1, use_defs e2)
  | Eor (e1, e2, _) ->
    eor (use_defs e1, use_defs e2)
  | Eimply (e1, e2, _) ->
    eimply (use_defs e1, use_defs e2)
  | Eequiv (e1, e2, _) ->
    let expr1 = use_defs e1 in
    let expr2 = use_defs e2 in
    eand (eimply (expr1, expr2), eimply (expr2, expr1))
  | Eall (x, s, e, _) ->
    eall (x, s, use_defs e)
  | Eex (x, s, e, _) ->
    eex (x, s, use_defs e)
  | Etau (x, s, e, _) ->
    let tau = etau (x, s, use_defs e) in
    if List.mem_assoc tau !new_terms
    then
      List.assoc tau !new_terms
    else
      let z = new_var () in
      new_terms := (tau, z) :: !new_terms;
      z
  | Elam (x, s, e, _) ->
    elam (x, s, use_defs e)
  | Emeta (x, _) ->
    assert false;
    (*let meta = emeta x in
    if List.mem_assoc meta !new_terms
    then
      List.assoc meta !new_terms
    else
      let z = new_var () in
      new_terms := (meta, e) :: !new_terms;
      z*)
and use_defs_rule rule =
  match rule with
  | Rfalse -> Rfalse
  | Rnottrue -> Rnottrue
  | Raxiom (p) -> Raxiom (use_defs p)
  | Rcut (p) -> Rcut (use_defs p)
  | Rnoteq (a) -> Rnoteq (use_defs a)
  | Reqsym (a, b) -> Reqsym (use_defs a, use_defs b)
  | Rnotnot (p) -> Rnotnot (use_defs p)
  | Rconnect (b, p, q) -> Rconnect (b, use_defs p, use_defs q) 
  | Rnotconnect (b, p, q) -> 
    Rnotconnect (b, use_defs p, use_defs q)
  | Rex (ep, v) -> Rex (use_defs ep, use_defs v) 
  | Rall (ap, t) -> Rall (use_defs ap, use_defs t)
  | Rnotex (ep, t) -> Rnotex (use_defs ep, use_defs t)
  | Rnotall (ap, v) -> Rnotall (use_defs ap, use_defs v)
  | Rpnotp (e1, e2) -> Rpnotp (use_defs e1, use_defs e2) 
  | Rnotequal (e1, e2) -> Rnotequal (use_defs e1, use_defs e2)
  | Rdefinition (name, sym, args, body, recarg, c, h) -> 
    rule
  | Rextension (ext, name, args, cons, hyps) ->
    Rextension (
      ext, name, List.map use_defs args, 
      List.map use_defs cons, List.map (List.map use_defs) hyps)
  | Rlemma (name, args) -> 
    assert false
  | RcongruenceLR (p, a, b) -> 
    RcongruenceLR (use_defs p, use_defs a, use_defs b)
  | RcongruenceRL (p, a, b) -> 
    RcongruenceRL (use_defs p, use_defs a, use_defs b)
  | Rroot (e) -> Rroot (use_defs e)

and use_defs_proof proof = 
  match proof.rule with
  | Rconnect (Equiv, p, q) ->
    let a = use_defs p in
    let b = use_defs q in
    let conc = List.map use_defs proof.conc in
    let conc0 = 
      eimply (a, b) :: eimply (b, a) :: conc in
    let conc1 = 
      enot a :: conc0 in
    let conc2 = 
      b :: conc0 in
    let conc3 = 
      a :: rm (eimply (b, a)) conc1 in
    let conc4 = 
      enot b :: rm (eimply (b, a)) conc2 in
    let hyp1, hyp2 = 
      match proof.hyps with
      | [h1; h2] -> use_defs_proof h1, use_defs_proof h2
      | _ -> assert false in
    {conc = conc;
     hyps = [
       {conc = conc0;
	hyps = [
	  {conc = conc1;
	   hyps = [hyp1; {
	     conc = conc3;
	     hyps = [];
	     rule = Raxiom (a)}];
	   rule = Rconnect (Imply, b, a)}; 
	  {conc = conc2;
	   hyps = [
	     {conc = conc4;
	      hyps = [];
	      rule = Raxiom (b)}; hyp2];
	   rule = Rconnect (Imply, b, a)}];
	rule = Rconnect (Imply, a, b)}];
     rule = Rconnect (And, eimply (a, b), eimply (b, a))}
  | Rnotconnect (Equiv, p, q) -> 
    let a = use_defs p in
    let b = use_defs q in
    let conc = List.map use_defs proof.conc in
    let conc1 = 
      enot (eimply (a, b)) :: conc in
    let conc2 = 
      enot (eimply (b, a)) :: conc in
    let hyp1, hyp2 = 
      match proof.hyps with
      | [h1; h2] -> use_defs_proof h1, use_defs_proof h2
      | _ -> assert false in
    {conc = conc;
     hyps = [
       {conc = conc1;
	hyps = [hyp2];
	rule = Rnotconnect (Imply, a, b)}; 
       {conc = conc2;
	hyps = [hyp1];
	rule = Rnotconnect (Imply, b, a)}];
     rule = Rnotconnect (And, eimply (a, b), eimply (b, a))}
  | Rlemma (name, args) ->
    use_defs_proof (Hashtbl.find lemma_env name)
(*  | Rnotconnect (Or, p, q) ->
    let a = use_defs p in
    let b = use_defs q in
    let conc = List.map use_defs proof.conc in
    let hyp =
      match proof.hyps with 
      | [h] -> use_defs_proof h
      | _ -> assert false in
    {conc = conc;
     hyps = [
       {conc = enot a :: conc;
	hyps = [hyp];
	rule = Rextension (
	  "", "zenon_rnotrightor", [], 
	  [enot (eor (a, b))], [[enot b]])}];
     rule = Rextension (
       "", "zenon_rnotleftor", [], 
    [enot (eor (a, b))], [[enot a]])}*)  
  | Rroot (p) -> 
    begin match proof.hyps with
    | [hyp] -> use_defs_proof hyp
    | _ -> assert false end
  | _ ->
    {conc = List.map use_defs proof.conc; 
     hyps = List.map use_defs_proof proof.hyps; 
     rule = use_defs_rule proof.rule}
;;

let rec union lists = 
  match lists with
  | [] -> [], []
  | [list] -> list, [[]]
  | [] :: lists -> 
    let main, remainders = union lists in
    main, main :: remainders
  | (x :: l) :: lists ->
    let main, remainders = union (l :: lists) in
    match remainders with
    | remainder :: remainders ->
      if inlist x main 
      then 
	if inlist x remainder
	then main, (rm x remainder) :: remainders
	else main, remainder :: remainders
      else
	x :: main, 
	remainder :: (List.map (fun xs -> x :: xs) remainders)
    | _ -> assert false
;;

let rec hypstoadd rule =
  match rule with
  | Rfalse -> [], [efalse]
  | Rnottrue -> [], [enot etrue]
  | Raxiom (p) -> [], [p; enot p]
  | Rcut (p) -> [[p]; [enot p]], []
  | Rnoteq (a) -> [], [enot (eapp ("=", [a; a]))]
  | Reqsym (a, b) -> 
    [], [eapp ("=", [a; b]); enot (eapp ("=", [b; a]))]
  | Rnotnot (p) -> [[p]], [enot (enot p)]
  | Rconnect (b, p, q) -> 
    begin match b with
    | And -> [[p; q]], [eand (p, q)]
    | Or -> [[p]; [q]], [eor (p, q)]
    | Imply -> [[enot p]; [q]], [eimply (p, q)]
    | Equiv -> assert false end
  | Rnotconnect (b, p, q) ->
    begin match b with
    | And -> [[enot p]; [enot q]], [enot (eand (p, q))]
    | Or -> [[enot p; enot q]], [enot (eor (p, q))]
    | Imply -> [[p; enot q]], [enot (eimply (p, q))]
    | Equiv -> assert false end
  | Rex (ep, v) -> 
    begin match ep with
    | Eex (x, ty, p, _) -> [[substitute [(x, v)] p]], [ep]
    | _ -> assert false end
  | Rall (ap, t) -> 
    begin match ap with
    | Eall (x, ty, p, _) -> [[substitute [(x, t)] p]], [ap]
    | _ -> assert false end
  | Rnotex (ep, t) -> 
    begin match ep with
    | Eex (x, ty, p, _) -> 
      [[enot (substitute [(x, t)] p)]], [enot ep]
    | _ -> assert false end
  | Rnotall (ap, v) -> 
    begin match ap with
    | Eall (x, ty, p, _) -> 
      [[enot (substitute [(x, v)] p)]], [enot ap]
    | _ -> assert false end
  | Rpnotp (e1, e2) -> 
    begin match e1, e2 with
    | Eapp (p, ts, _), Enot (Eapp (q, us, _), _) ->
      List.map2 
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us, 
      [e1; e2]
    | _ -> assert false end
  | Rnotequal (e1, e2) -> 
    begin match e1, e2 with
    | Eapp (p, ts, _), Eapp (q, us, _) ->
      List.map2 
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us, 
      [enot (eapp ("=", [e1; e2]))]
    | _ -> assert false end
  | RcongruenceLR (p, a, b) -> 
    [[apply p b]], [apply p a; eapp ("=", [a; b])]
  | RcongruenceRL (p, a, b) -> 
    [[apply p b]], [apply p a; eapp ("=", [b; a])]
  | Rextension (ext, name, args, concs, hyps) ->
    hyps, concs
  | Rlemma (name, args) ->
    assert false;
  | Rroot (e) -> [[e]], [e]
  | _ -> assert false 
;;

let rec lladdhyp l prf =
  {conclusion = prf.conclusion;
   gamma = l @ prf.gamma; 
   newhyps = List.map (lladdhyp l) prf.newhyps;
   newrule = prf.newrule;
   contracted = prf.contracted}
;;

let rec useful e proof = 
  let gamma = proof.gamma in
  let hyps = proof.newhyps in
  let hypslist, _ = hypstoadd proof.newrule in
  if inlist e proof.conclusion
  then
    let bool = List.for_all2
      (fun h l -> List.exists (fun f -> useful f h) l) 
      hyps hypslist in
    if inlist e gamma  
    then bool && List.exists (useful e) hyps
    else bool    
  else 
    List.exists (useful e) hyps
;;

let rec clean e proof =
  let gamma = proof.gamma in
  let hyps = proof.newhyps in
  let hypslist, _ = hypstoadd proof.newrule in
  let result1 = 
    if inlist e gamma && not (List.exists (useful e) hyps) 
    then
      let list = List.fold_left 
	(fun hypos hypolist -> 
	  List.fold_left
	    (fun partial hypo -> 
	      (List.map (fun l -> l@[hypo]) hypos) @ partial)
	    [] hypolist)
	[[]] (List.map (clean e) hyps) in
      List.map
	(fun l ->
	  {conclusion = proof.conclusion;
	    gamma = rm e proof.gamma; 
	    newhyps = l;
	    newrule = proof.newrule;
	    contracted = proof.contracted}) list
    else [] in
  if inlist e proof.conclusion
  then
    let hypos = List.filter 
      (fun (prf, l) -> List.exists (fun f -> useful f prf) l)
      (List.combine hyps hypslist) in
    let result2 = 
      List.flatten (
	List.map
	  (fun (prf, l) ->
	    let others = rm e proof.conclusion in
	    List.map (lladdhyp others)
	      (List.fold_left
		 (fun prfs f -> List.flatten (
		   List.map (clean f) prfs))
		 [prf] l))
	    hypos) in
    result1 @ result2
  else result1
;;

let rec addcontrs proof gamma =
  let hypslist, conclist = hypstoadd proof.rule in
  let newcontr, list =
    List.fold_left (fun (cs, es) e -> 
      if (inlist e es) 
      then
	cs, rm e es
      else
	e :: cs, es)
      ([], gamma) conclist in
  let contrshyps = List.map2 addcontrs proof.hyps
    (List.map (List.rev_append list) hypslist) in
  let contrs, prehyps = List.split contrshyps in
  let maincontr, remainders = union contrs in
  let hyps = List.map2 lladdhyp remainders prehyps in
  let (contracted, remaining) =
    List.fold_left
      (fun (contracted, remaining) c ->
	if inlist c conclist
	then c :: contracted, remaining
	else contracted, c :: remaining)
      ([], newcontr) maincontr in
  remaining, {
    conclusion = conclist;
    gamma = list@maincontr;
    newhyps = hyps;
    newrule = proof.rule;
    contracted = contracted}

and lltolk proof goal =
  let newproof = use_defs_proof proof in
  let right, newgoal, newgamma =
    match goal with
    | Some (Enot (g, _)) -> 
      let ng = use_defs g in
      [ng], ng, (enot ng) :: List.map use_defs !hypothesis_env
    | None -> [], efalse, List.map use_defs !hypothesis_env
    | _ -> assert false in
  let l, newproof = addcontrs newproof newgamma in
  assert (l = []);
  let lkproof = lltolkrule newproof right in
  newgoal, lkproof

and lltolkrule proof right =
  match right with
  | [r] when inlist r proof.contracted &&
      oneinlist r (proof.gamma @ proof.conclusion) ->
      let prf = xlltolkrule proof [] in
      lefttoright r 
	(List.fold_left
	   (fun prf c -> sclcontr (c, prf))
	   prf proof.contracted)
  | _ ->
      let prf = xlltolkrule proof right in
      List.fold_left
	(fun prf c -> sclcontr (c, prf))
	prf proof.contracted

and xlltolkrule proof right =
  let gamma = proof.gamma in
  match proof.newrule, proof.newhyps, right with
  | Rfalse, [], [] ->
    scfalse (gamma, efalse)
  | Rfalse, [], [r] ->
    scfalse (rm (enot r) gamma, r)
  | Rnottrue, [], [] ->
    righttoleft etrue (sctrue (gamma))
  | Rnottrue, [], [Etrue] ->
    sctrue (gamma)
  | Rnottrue, [], [r] ->
    scrweak (r, sclnot (etrue, sctrue (rm (enot r) gamma)))
  | Raxiom p, [], [] -> 
    righttoleft p (scaxiom (p, gamma))
  | Raxiom p, [], [r] when equal r p ->
    scaxiom (p, gamma)
  | Raxiom p, [], [r] when not (equal (enot r) p) ->
    scrweak (r, sclnot (p, scaxiom (p, gamma)))
  | Rcut p, [proof1; proof2], [] ->
    let prf1 = lltolkrule proof1 [] in
    let prf2 = lltolkrule proof2 [] in
    sccut (enot p, scrnot (p, prf1), prf2)
  | Rcut p, [proof1; proof2], [r] 
    when not (useful (enot r) proof1) ->
    let prf1 = lltolkrule (List.hd (clean (enot r) proof1)) [] in
    let prf2 = lltolkrule proof2 [r] in
    sccut (enot p, scrnot (p, prf1), prf2)
  | Rcut p, [proof1; proof2], [r] 
    when not (useful (enot r) proof2) ->
    let prf1 = lltolkrule (List.hd (clean (enot r) proof2)) [p] in
    let prf2 = lltolkrule proof1 [r] in
    sccut (p, prf1, prf2)
  | Rnoteq a, [], [] -> 
    righttoleft (eapp ("=", [a; a])) (sceqref (a, gamma))
  | Rnoteq a, [], [r] when equal r (eapp ("=", [a; a])) ->
    sceqref (a, gamma)
  | Rnoteq a, [], [r] ->
    scrweak (r, sclnot (
      eapp ("=", [a; a]), 
      sceqref (a, rm (enot r) gamma)))
  | Reqsym (a, b), [], [] ->
    righttoleft (eapp ("=", [b; a]))
      (sceqsym (a, b, gamma))
  | Reqsym (a, b), [], [r] when equal r (eapp ("=", [b; a])) ->
    sceqsym (a, b, gamma)
  | Reqsym (a, b), [], [r] ->
    scrweak (r, sclnot (
      eapp ("=", [b; a]), 
      sceqsym (a, b, rm (enot r) gamma)))
  | Rnotnot p, [proof], [] ->
    let prf = lltolkrule proof [] in
    righttoleft (enot (p))
      (scrnot (p, prf))
  | Rnotnot p, [proof], [r] 
    when equal r (enot p) ->
    let prf = lltolkrule proof [] in
    scrnot (p, prf)
  | Rconnect (And, p, q), [proof], _ ->
    let prf = lltolkrule proof right in
    scland (p, q, prf)
  | Rconnect (Or, p, q), [proof1; proof2], _ ->
    let prf1 = lltolkrule proof1 right in
    let prf2 = lltolkrule proof2 right in
    sclor (p, q, prf1, prf2)
  | Rconnect (Imply, p, q), [proof1; proof2], [] ->
    let prf1 = lltolkrule proof1 [] in
    let prf2 = lltolkrule proof2 [] in
    make_imply p q prf1 prf2;
  | Rconnect (Imply, p, q), [proof1; proof2], [r] 
    when not (useful (enot r) proof1) ->
    let prf1 = lltolkrule (List.hd (clean (enot r) proof1)) [p] in
    let prf2 = lltolkrule proof2 [r] in
    sclimply (p, q, prf1, prf2)
  | Rconnect (Imply, p, q), [proof1; proof2], [r] 
    when not (useful (enot r) proof2) ->
    let prf1 = lltolkrule proof1 [r] in
    let prf2 = lltolkrule (List.hd (clean (enot r) proof2)) [] in
    make_imply p q prf1 prf2
  | Rnotconnect (And, p, q), [proof1; proof2], [] ->
    let prf1 = lltolkrule proof1 [] in
    let prf2 = lltolkrule proof2 [] in
    make_not_and_l p q prf1 prf2
  | Rnotconnect (And, p, q), [proof1; proof2], [r] 
    when (equal r (eand (p, q))) ->
    let prf1 = lltolkrule proof1 [p] in
    let prf2 = lltolkrule proof2 [q] in
    scrand (p, q, prf1, prf2)
  | Rnotconnect (And, p, q), [proof1; proof2], [r] 
    when not (useful (enot r) proof1) ->
    let prf1 = lltolkrule (List.hd (clean (enot r) proof1)) [] in
    let prf2 = lltolkrule proof2 [r] in
    make_not_and_r p q prf1 prf2
  | Rnotconnect (And, p, q), [proof1; proof2], [r] 
    when not (useful (enot r) proof2) ->
    let prf1 = lltolkrule proof1 [r] in
    let prf2 = lltolkrule (List.hd (clean (enot r) proof2)) [] in
    make_not_and_l p q prf1 prf2  
  | Rnotconnect (Or, p, q), [proof], [] ->
    let prf = lltolkrule proof [] in
    make_not_or p q prf
  | Rnotconnect (Or, p, q), [proof], [r] 
    when (equal r (eor (p, q)) && not (useful (enot p) proof)) ->
    let prf = lltolkrule (List.hd (clean (enot p) proof)) [q] in
    scrorr (p, q, prf)
  | Rnotconnect (Or, p, q), [proof], [r] 
    when (equal r (eor (p, q)) && not (useful (enot q) proof)) ->
    let prf = lltolkrule (List.hd (clean (enot q) proof)) [p] in
    scrorl (p, q, prf)
  | Rnotconnect (Or, p, q), [proof], [r] 
    when (not (equal r (eor (p, q)))) ->
    let prf = lltolkrule proof [r] in
    make_not_or p q prf
  | Rnotconnect (Imply, p, q), [proof], [] ->
    let prf = lltolkrule proof [] in
    make_not_imply p q prf
  | Rnotconnect (Imply, p, q), [proof], [r] 
    when (equal r (eimply (p, q))) ->
    let prf = lltolkrule proof [q] in
    scrimply (p, q, prf)
  | Rnotconnect (Imply, p, q), [proof], [r] ->
    let prf = lltolkrule proof [r] in
    make_not_imply p q prf
  | Rex (ep, v), [proof], _ ->
    let prf = lltolkrule proof right in
    sclex (ep, v, prf)
  | Rall (ap, t), [proof], _ ->
    let prf = lltolkrule proof right in
    sclall (ap, t, prf)
  | Rnotex (Eex(x, _, p, _) as ep, t), [proof], [] ->
    let prf = lltolkrule proof [] in
    make_not_exists (substitute [(x, t)] p) ep t prf
  | Rnotex (Eex(x, _, p, _) as ep, t), [proof], [r] 
    when (equal r ep) ->
    let prf = lltolkrule proof [substitute [(x, t)] p] in
    screx (ep, t, prf)
  | Rnotex (Eex(x, _, p, _) as ep, t), [proof], [r] ->
    let prf = lltolkrule proof [r] in
    make_not_exists (substitute [(x, t)] p) ep t prf  
  | Rnotall (Eall(x, _, p, _) as ap, v), [proof], [] ->
    let prf = lltolkrule proof [substitute [(x, v)] p] in
    righttoleft ap (scrall (ap, v, prf))
  | Rnotall (Eall(x, _, p, _) as ap, v), [proof], [r] 
    when (equal r ap) ->
    let prf = lltolkrule proof [substitute [(x, v)] p] in
    scrall (ap, v, prf)
  | Rpnotp (Eapp (_, ts, _) as e1, 
	    Enot (Eapp (_, us, _) as e2, _)), proofs, [] ->
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let prfs = 
      List.map2 (fun p eq -> lltolkrule p [eq]) proofs eqs in
    righttoleft e2 (sceqpropbis (e1, e2, prfs, gamma))
  | Rnotequal (Eapp (_, ts, _) as e1,
	       (Eapp (_, us, _) as e2)), proofs, [] ->
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let prfs = 
      List.map2 (fun p eq -> lltolkrule p [eq]) proofs eqs in
    righttoleft (eapp ("=", [e1; e2])) 
      (sceqfuncbis (e1, e2, prfs, gamma))
  | RcongruenceLR (p, a, b), [proof], [] ->
    let prf = lltolkrule proof [] in
    let g, c, rule = prf in
    begin match p with
    | Elam (x, ty, e, _) ->
      let prf1 = 
	addhyp (rm (apply p b) g) (rmcongruence true x e a b) in
      let prf2 = addhyp [apply p a; eapp ("=", [a; b])] prf in
      assert (gamma_length prf2 = 
	  gamma_length prf1 + 1);
  (*p_debug "sccut" [apply p b];
  p_debug_prf "of prf1" prf1;
  p_debug_prf "and prf2" prf2;*)
      sccut (
	apply p b, 
	addhyp (rm (apply p b) g) (rmcongruence true x e a b), 
	addhyp [apply p a; eapp ("=", [a; b])] prf)
    | _ -> assert false end
  | RcongruenceRL (p, a, b), [proof], [] ->
    let prf = lltolkrule proof [] in
    let g, c, rule = prf in
    begin match p with
    | Elam (x, ty, e, _) ->
      let prf1 = 
	addhyp (rm (apply p b) g) (rmcongruence false x e a b) in
      let prf2 = addhyp [apply p a; eapp ("=", [a; b])] prf in
      assert (gamma_length prf2 = 
	  gamma_length prf1 + 1);
      sccut (
	apply p b, 
	addhyp (rm (apply p b) g) (rmcongruence false x e a b), 
	addhyp [apply p a; eapp ("=", [a; b])] prf)
    | _ -> assert false end  
  | Rdefinition (name, sym, args, body, recarg, fld, unf), [proof] 
   , [] -> lltolkrule proof []
  | Rextension (
    "", "zenon_notallex", [Elam (v, t, p, _)], 
    [Enot (Eall (x, s, e, _) as ap, _)], [[ep]]), [proof], [] ->
    let prf = lltolkrule proof [] in
    let g, c, rule = prf in
    begin match rule with
    | SClex (exp, y, prf0) 
	when (equal exp ep) -> 
      let q = substitute [(v, y)] p in
      assert (ingamma (enot q) prf0);
      righttoleft ap
	(scrall (
	  ap, y, lefttoright q prf0))
    | _ ->
      let z = new_var () in
      let q = substitute [(v, z)] p in
      righttoleft ap
	(scrall (
	  ap, z, lefttoright q (
	    sccut (
	      ep,
	      screx (
		ep, z, scaxiom (
		  enot q, gamma)), 
	      addhyp [enot q]  prf)))) end
  | Rextension ("", "zenon_stringequal", [s1; s2], [c], []), 
      [], [] ->
    let v1 = eapp ("$string", [s1]) in
    let v2 = eapp ("$string", [s2]) in
    let n1 = List.assoc v1 !distinct_terms in
    let n2 = List.assoc v2 !distinct_terms in
    let c = eapp ("=", [v1; v2]) in
    if n1 < n2
    then righttoleft c (scaxiom (c, rm (enot c) gamma))
    else righttoleft c (sceqsym (v1, v2, rm (enot c) gamma))
  | Rextension (
    "", "zenon_stringdiffll", [e1; v1; e2; v2], 
    [c1; c2], [[h]]), [proof], [] ->
    let prf = lltolkrule proof [] in
    deduce_inequality e1 e2 v1 v2 c1 c2 true true gamma prf
  | Rextension (
    "", "zenon_stringdifflr", [e1; v1; e2; v2], 
    [c1; c2], [[h]]), [proof], [] ->
    let prf = lltolkrule proof [] in
    deduce_inequality e1 e2 v1 v2 c1 c2 true false gamma prf
  | Rextension (
    "", "zenon_stringdiffrl", [e1; v1; e2; v2], 
    [c1; c2], [[h]]), [proof], [] ->
    let prf = lltolkrule proof [] in
    deduce_inequality e1 e2 v1 v2 c1 c2 false true gamma prf
  | Rextension (
    "", "zenon_stringdiffrr", [e1; v1; e2; v2], 
    [c1; c2], [[h]]), [proof], [] ->
    let prf = lltolkrule proof [] in
   deduce_inequality e1 e2 v1 v2 c1 c2 false false gamma prf
  | _, _, [r] ->
    lefttoright r (xlltolkrule proof [])  
  | Rextension (ext, name, args, cons, hyps), proofs, [] -> 
    assert false
  | Rlemma (name, args), [], [] -> 
    assert false
  | Rconnect (Equiv, p, q), _, _ ->
    assert false
  | Rnotconnect (Equiv, p, q), [proof1; proof2], [] ->
    assert false
  | _ -> assert false

and addtogamma proof =
  let _, _, rule = proof in
  match rule with
  | SClnot (e, _) -> enot e
  | SClimply (e1, e2, _, _) -> eimply (e1, e2)
  | SCland (e1, e2, _) -> eand (e1, e2)
  | SClor (e1, e2, _, _) -> eor (e1, e2)
  | SClall (e, _, _) -> e
  | SClex (e, _, _) -> e
  | _ -> assert false
      
and removeinhyps proof =
  let _, _, rule = proof in
  match rule with
  | SCcnot (e, _) -> [[enot e]]
  | SCrimply (e1, _, _) -> [[e1]]
  | SCrnot (e, _) -> [[e]]
  | SClcontr (e, _) -> [[e]]
  | SCrand _ -> [[]; []]
  | SCrweak _ | SCrorl _ | SCrorr _ | SCrall _ | SCrex _ -> [[]]
  | SClnot (e, _) -> [[]]
  | SClimply (e1, e2, _, _) -> [[];[e2]]
  | SCland (e1, e2, _) -> [[e1; e2]]
  | SClor (e1, e2, _, _) -> [[e1]; [e2]]
  | SClall (Eall (x, _, e, _), t, _) -> [[substitute [(x, t)] e]]
  | SClex (Eex (x, _, e, _), v, _) -> [[substitute [(x, v)] e]] 
  | SCcut (e, _, _) -> [[]; [e]]
  | _ -> assert false

and ntimes n e1 e2 g =
  assert (inlist e2 g);
  if n = 1 then e1 :: (rm e2 g)
  else e1 :: (rm e2 (ntimes (n-1) e1 e2 g))

(* transforme proof = gamma, enot p |- c en 
   gamma, big |- c
   avec cons : prf delta |- p => prf delta, big |- *)
and adaptproof proof p big cons =
  let rec xmake proof n = 
    let g, c, rule = proof in
    match rule with
    | SClnot (e, prf) when (equal e p) ->
      if n = 1 then cons prf else cons (xmake prf (n-1))
    | SClcontr (e, prf) when (equal e (enot p) && 
	n = List.length (List.filter (equal (enot p)) g)) ->
      sclcontr (big, xmake prf (n+1))
    | SCaxiom e when (equal e (enot p) && 
        n = List.length (List.filter (equal (enot p)) g)) ->
      scrnot (p, xmake (sclnot (p, scaxiom (p, rm e g))) n)
    | SClnot _ | SCland _ | SClor _ | SClall _ | SClex _ | SCrweak _
    | SCcnot _ | SCrimply _ | SCrnot _ | SClcontr _ | SClimply _ 
    | SCrand _ | SCrorl _ | SCrorr _ | SCrall _ | SCrex _ | SCcut _
      -> 
      applytohyps2 (List.map (
	fun hs -> (fun prf -> xmake prf n)) (removeinhyps proof)) 
	proof
    | SCaxiom _ | SCfalse | SCtrue | SCeqref _ 
    | SCeqsym _ | SCeqprop _ | SCeqfunc _ 
      -> (ntimes n big (enot p) g), c, rule in
  xmake proof 1
      
(* transforme proof1 = gamma, enot p |- c en 
   gamma, big |- c
   avec proof2 = gamma, x |- y
   cons : prf delta |- p, prf delta, x |- y => prf delta, big |- *)
and makeproof proof1 proof2 p big cons =
  let rec xmake proof l1 l2 n = 
    let g, c, rule = proof in
    match rule with
    | SClnot (e, prf) when (equal e p) ->
      if n = 1 then
	cons (addhyp l1 prf) (addhyp l2 proof2)
      else
	cons (xmake prf l1 (rm big l2) (n-1)) (addhyp l2 proof2)
    | SClcontr (e, prf) when (equal e (enot p) && 
	n = List.length (List.filter (equal (enot p)) g)) ->
      sclcontr (big, xmake prf l1 (big :: l2) (n+1))
    | SCaxiom e when (equal e (enot p) && 
        n = List.length (List.filter (equal (enot p)) g)) ->
      scrnot (
	p, xmake (sclnot (
	  p, scaxiom (p, rm e g))) l1 (p :: l2) n)
    | SClnot _ | SClimply _ | SCland _ | SClor _ 
    | SClall _ | SClex _
      -> 
      let e = addtogamma proof in
      if inlist e l2
      then
	applytohyps2 (List.map (
	  fun hs -> (fun prf -> xmake prf l1 (hs @ (rm e l2)) n)) ( 
	  removeinhyps proof)) proof
      else
	sclcontr (e, applytohyps2 (List.map (
	  fun hs -> (fun prf -> xmake prf (e :: l1) (hs @ l2) n)) ( 
	  removeinhyps proof)) proof)
    | SCcnot _ | SCrimply _ | SCrnot _ | SClcontr _ | SCrweak _ 
    | SCrand _ | SCrorl _ | SCrorr _ | SCrall _ | SCrex _ | SCcut _
      -> applytohyps2 (List.map (
	fun hs -> (fun prf -> xmake prf l1 (hs @ l2) n)) (
	removeinhyps proof)) proof
    | SCaxiom _ | SCfalse | SCtrue | SCeqref _ 
    | SCeqsym _ | SCeqprop _ | SCeqfunc _ 
      -> (ntimes n big (enot p) g)@l1, c, rule in
  xmake proof1 [] [] 1
      
and make_imply p q proof1 proof2 =
  makeproof proof1 proof2 p (eimply (p, q)) 
    (fun prf1 prf2 -> sclimply (p, q, prf1, prf2))
(* (gamma, not p |- c), (gamma, not q |- ) *)
and make_not_and_l p q proof1 proof2 =
  makeproof proof1 proof2 p (enot (eand (p, q))) 
    (fun prf1 prf2 -> 
      makeproof prf2 prf1 q (enot (eand (p, q))) 
	(fun pr1 pr2 -> 
	  sclnot (eand (p, q), scrand (p, q, pr2, pr1))))
and make_not_and_r p q proof1 proof2 =
  makeproof proof2 proof1 q (enot (eand (p, q))) 
    (fun prf1 prf2 -> 
      makeproof prf2 prf1 p (enot (eand (p, q))) 
	(fun pr1 pr2 -> 
	  sclnot (eand (p, q), scrand (p, q, pr1, pr2))))
and make_not_or p q proof =
  sclcontr (
    enot (eor (p, q)), 
    adaptproof 
      (adaptproof proof q (enot (eor (p, q)))
	 (fun prf -> sclnot (eor (p, q), scrorr (p, q, prf))))
      p (enot (eor (p, q)))
      (fun prf -> sclnot (eor (p, q), scrorl (p, q, prf))))
and make_not_imply p q proof = 
  sclcontr (enot (eimply (p, q)), sclnot (
    eimply (p, q), scrimply (p, q, scrweak (
      q, adaptproof proof q (enot (eimply (p, q)))
	(fun prf -> sclnot (
	  eimply (p, q), scrimply (p, q, addhyp [p] prf)))))))
and make_not_exists sub ep t proof =
  adaptproof proof sub (enot ep)
    (fun prf -> sclnot (ep, screx (ep, t, prf)))
    
and righttoleft e proof =
  let g, c, rule = proof in
  let ne = enot e in
  match rule with
  | SCcnot (f, prf) -> prf
  | SClnot _ -> assert false
  | SClimply (f1, f2, prf1, prf2) ->
    sclimply (f1, f2, xaddhyp ne prf1, righttoleft e prf2)
  | SCcut (f, prf1, prf2) ->
    sccut (f, xaddhyp ne prf1, righttoleft e prf2)
  | SCland _ | SClor _ | SClall _ | SClex _
    -> applytohyps (righttoleft e) proof
  | SCaxiom _ | SCfalse | SCtrue | SCeqref _ | SCeqsym _
  | SCeqprop _ | SCeqfunc _ | SCrweak _
    -> sclnot (e, proof)
  | SCrand _ | SCrorl _ | SCrorr _ 
  | SCrimply _ | SCrnot _ | SCrall _ | SCrex _ | SClcontr _
    -> sclnot (e, proof)
    
and lefttoright e proof =
  let g, c, rule = proof in
  let ne = enot e in
  assert (inlist ne g);
  if not (lkuseful ne proof)
  then scrweak (e, lkclean ne proof)
  else
    match e with
    | Enot (f, _) -> 
      optimize (scrnot (f, rmdblnot f proof))
    | _ -> 
      assert (equal c efalse);
      assert (ingamma ne proof);
      match rule with
      | SClnot (f, prf) 
	  when (equal f e) -> prf
      | SClcontr (f, _) 
	  when (equal ne f) -> sccnot (e, proof)
      | SClimply (a, b, prf1, prf2)
	  when (not (lkuseful ne prf1)) ->
	sclimply (a, b, lkclean ne prf1, lefttoright e prf2)
      | SCcut (a, prf1, prf2)
	  when (not (lkuseful ne prf1)) ->
	sccut (a, lkclean ne prf1, lefttoright e prf2)
      | SClnot _ | SCcut _ | SClimply _ -> 
	sccnot (e, proof)
      | SCaxiom _ | SCfalse -> 
	scfalse (rm efalse (rm ne g), e)
      | SClcontr _ | SClor _ | SCland _ | SClex _ | SClall _
	-> applytohyps (lefttoright e) proof
      | SCrex _ | SCrall _ | SCrand _ | SCrorr _ | SCrorl _
      | SCrimply _ | SCrnot _ | SCeqfunc _ | SCeqprop _ 
      | SCeqsym _ | SCeqref _ | SCtrue | SCcnot _ | SCrweak _
	-> assert false	  

and rmdblnot e proof =  
  let g, c, rule = proof in
  match rule with
  | SClnot (Enot (f, _), prf) when equal f e ->
    xrmdblnot e prf
  | SCaxiom (Enot (Enot (f, _), _)) when equal f e ->
    scrnot (
      enot e, sclnot (e, scaxiom (e, rm (enot (enot e)) g)))
  | SCaxiom (f) -> scaxiom (f, e :: (rm f (rm (enot (enot e)) g)))
  | SCfalse -> scfalse (e :: rm (enot (enot e)) g, c)
  | SCtrue -> sctrue (e :: rm (enot (enot e)) g)
  | SCeqref (a) -> sceqref (a, e :: rm (enot (enot e)) g)
  | SCeqsym (a, b) -> sceqsym (a, b, e :: rm (enot (enot e)) g)
  | SCeqprop (a, b) -> sceqprop (a, b, e :: rm (enot (enot e)) g)
  | SCeqfunc (a, b) -> sceqfunc (a, b, e :: rm (enot (enot e)) g)
  | SClcontr (Enot (Enot (f, _), _), prf) when equal f e ->
    sclcontr (f, rmdblnot e (rmdblnot e prf))
  | SCcut (_, prf1, prf2) -> applytohyps (rmdblnot e) proof
  | _ -> applytohyps (rmdblnot e) proof

and xrmdblnot e proof =
  let g, c, rule = proof in
  match rule with
  | SCaxiom (Enot (f, _)) ->
    assert (equal f e);
    sclnot (f, scaxiom (f, rm (enot f) g))
  | SCeqprop _ | SCeqfunc _ | SCtrue | SCeqref _ | SCeqsym _ 
  | SCrimply _ | SCrand _ | SCrorl _ | SCrorr _  
  | SCrall _ | SCrex _ -> assert false
  | SCfalse -> scfalse (e :: (rm efalse g), efalse)
  | SClnot (f, prf) -> addhyp [e] prf
  | SCrnot (f, prf) -> assert (equal f e); prf
  | _ -> assert false;

and optimize proof =
  let g, c, rule = proof in
  match rule with
  | SCcnot (e, prf) ->
    lefttoright e prf
  | SClnot (e, prf) -> 
    righttoleft e prf
  | _ -> applytohyps optimize proof

and lkclean f prf = 
  let g, c, rule = prf in
  match rule with
  | SCeqsym _ | SCeqref _ 
  | SCtrue | SCaxiom _ | SCfalse
  | SCeqprop _ | SCeqfunc _ -> 
    assert (inlist f g);
    rm f g, c, rule
  | _ -> applytohyps (lkclean f) prf

and lkuseful e proof =
  let g, c, rule = proof in
  match rule with
  | SCeqsym (a, b) -> 
    equal e (eapp ("=", [a; b])) && not (inlist e (rm e g))
  | SCeqref (a) -> false
  | SCtrue -> false
  | SCaxiom (a) -> equal e a && not (inlist e (rm e g))
  | SCfalse -> equal e efalse && not (inlist e (rm e g))
  | SCeqprop (Eapp (p, ts, _) as f1, Eapp (_, us, _)) ->
    let x = equal e f1 in
    List.fold_left2 
      (fun x t u -> (x || equal e (eapp ("=", [t; u]))))
      x ts us
  | SCeqprop _ -> assert false
  | SCeqfunc (Eapp (p, ts, _), Eapp (_, us, _)) ->
    List.fold_left2 
      (fun x t u -> (x || equal e (eapp ("=", [t; u]))))
      false ts us 
  | SCeqfunc _ -> assert false
  | SClcontr (f, _) 
      when (equal e f && not (inlist e (rm e g))) -> true
  | SClor (a, b, _, _) 
      when (equal e (eor (a, b)) 
	    && not (inlist e (rm e g))) -> true
  | SCland (a, b, _)
      when (equal e (eand (a, b)) 
	    && not (inlist e (rm e g))) -> true
  | SClex (f, _, _)
      when (equal e f && not (inlist e (rm e g))) -> true
  | SClall (f, _, _)
      when (equal e f && not (inlist e (rm e g))) -> true
  | SClnot (f, _)
      when (equal e (enot f) && not (inlist e (rm e g))) -> true
  | SClimply (a, b, _, _)
      when (equal e (eimply (a, b))
	    && not (inlist e (rm e g))) -> true
  | SClcontr _ | SClor _ | SCland _ | SClex _
  | SClall _ | SClnot _ | SClimply _ | SCcut _
  | SCrimply _ | SCrnot _ | SCrex _ | SCrall _ 
  | SCrand _ | SCrorr _ | SCrorl _ | SCrweak _ | SCcnot _
    -> List.exists (lkuseful e) (hypsofrule rule)

and deduce_inequality e1 e2 v1 v2 c1 c2 b1 b2 gamma proof =
  let n1 = List.assoc v1 !distinct_terms in
  let n2 = List.assoc v2 !distinct_terms in
  let eq = eapp ("=", [e1; e2]) in
  let b3 = n1 < n2 in
  let ax = 
    if b3
    then eapp ("=", [v1; v2])
    else eapp ("=", [v2; v1]) in
  let rec f b1 b2 b3 = 
    match b1, b2, b3 with
    | true, true, true -> sceqprop (eq, ax, [])
    | _, _, false -> 
      sccut (
	eapp ("=", [v1; v2]),
	f b1 b2 true, sceqsym (v1, v2, [c1; c2; eq]))
    | _, false, _ -> 
      sccut (
	eapp ("=", [e2; v2]),
	sceqsym (v2, e2, [c1; eq]), addhyp [c2] (f b1 true b3))
    | false, _, _ ->
      sccut (
	eapp ("=", [e1; v1]),
	sceqsym (v1, e1, [c2; eq]), addhyp [c1] (f true b2 b3))
  in
  sccut (
    enot eq,
    addhyp (rm (enot ax) gamma) (
      scrnot (eq, sclnot (ax, (f b1 b2 b3)))),
    addhyp [c1; c2] proof)

and constructive proof = 
  let (g, c, rule) = proof in
  match rule with
  | SCcnot _ -> false
  | _ -> List.fold_left 
    (fun b prf -> b && constructive prf) true (hypsofrule rule)

and rmcongruence s x e a b =
  let eq = 
    if s
    then eapp ("=", [a; b])
    else eapp ("=", [b; a]) in
  match e with
  | Etrue | Efalse | Evar _ -> scaxiom (e, [])
  | Eapp (f, args, _) -> 
    sceqpropbis (
      substitute [(x, a)] e, substitute [(x, b)] e, 
      List.map (fun t -> xrmcongruence s x t a b) args, [eq])
  | Eand (e1, e2, _) ->
    scland (
      substitute [(x, a)] e1, substitute [(x, a)] e2,
      scrand (
	substitute [(x, b)] e1, substitute [(x, b)] e2, 
	addhyp [substitute [(x, b)] e2] (rmcongruence s x e1 a b), 
	addhyp [substitute [(x, b)] e1] (rmcongruence s x e2 a b))) 
  | Eor (e1, e2, _) ->
    sclor (
      substitute [(x, a)] e1, substitute [(x, a)] e2,
      scrorl (
	substitute [(x, b)] e1, substitute [(x, b)] e2, 
	rmcongruence s x e1 a b),
      scrorr (
	substitute [(x, b)] e1, substitute [(x, b)] e2, 
	rmcongruence s x e2 a b))
  | Eimply (e1, e2, _) ->
    scrimply (
      substitute [(x, b)] e1, substitute [(x, b)] e2,
      sclimply (
	substitute [(x, a)] e1, substitute [(x, a)] e2,
	rmcongruence (not s) x e1 b a,
	addhyp [substitute [(x, b)] e1] (rmcongruence s x e2 a b)))
  | Enot (e0, _) -> 
    scrnot (
      substitute [(x, b)] e0,
      sclnot (
	substitute [(x, a)] e0,
	rmcongruence (not s) x e0 b a))
  | Eall (y, ty, e0, _) ->
    let z = new_var () in
    scrall (
      substitute [(x, b)] e, 
      substitute [(x, b)] z,
      sclall (
	substitute [(x, a)] e, 
	substitute [(x, a)] z,
	rmcongruence s x 
	  (substitute [(y, z)] e0) a b))
  | Eex (y, ty, e0, _) ->
    let z = new_var () in
    screx (
      substitute [(x, b)] e, 
      substitute [(x, b)] z,
      sclex (
	substitute [(x, a)] e, 
	substitute [(x, a)] z,
	rmcongruence s x 
	  (substitute [(y, z)] e0) a b))
    | Etau _ | Elam _ | Emeta _ | Eequiv _ ->
    assert false
      
and xrmcongruence s x t a b =
  let eq = 
    if s
    then eapp ("=", [a; b])
    else eapp ("=", [b; a]) in
  match t with
  | Evar (v, _) when (equal x t) -> 
    if s
    then scaxiom (eapp ("=", [a; b]), []) 
    else sceqsym (b, a, [])
  | Evar _ | Etau _ -> sceqref (t, [eq])
  | Eapp (f, args, _) -> 
    sceqfuncbis (
      substitute [(x, a)] t, substitute [(x, b)] t, 
      List.map (fun t -> xrmcongruence s x t a b) args, [eq]) 
  | _ -> assert false  
;;

let rec lltolj proof goal =

  let result = lltolk proof goal in
  let conc, lkproof = List.fold_left
    (fun (conc, rule) stmt ->
      let newstmt = use_defs stmt in
      eimply (newstmt, conc), 
      scrimply (newstmt, conc, rule)
    )
    result !hypothesis_env in
  let _, ljproof = lltoljrule (*optimize lkproof*)lkproof in
  ljproof
    
and lltoljrule lkproof =
  (*p_debug_proof "\nseq" lkproof;*)
  let lkg, lkc, rule = lkproof in
  let assocs, proofs =
    List.split (List.map lltoljrule (hypsofrule rule)) in
  let ljlist, ljprf =
  match rule, assocs, proofs with
    | SCcut (a, lklkprf1, lklkprf2), [l1; l2],
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      (*let lklkg1, _, _ = lklkprf1 in
      let lklkg2, _, _ = lklkprf2 in
      eprintf "\ncut : %d %d\n" (List.length lklkg1) 
	(List.length lklkg2);
      eprintf "\ncut : %d %d\n" (List.length l1) 
	(List.length l2);
      eprintf "\ncut : %d %d\n" (List.length g1) 
	(List.length g2);*)
      let l = merge [l1; List.remove_assoc a l2] in
      (*
      let lx, ly = List.split l in p_debug "lx" lx; p_debug "ly" ly;
      let x, y = List.split l1 in p_debug "lx1" x; p_debug "ly1" y;
      *)let q1 = replace l l1 in
      let q2 = replace l (List.remove_assoc a l2) in
      newcut l (List.assoc a l2)
	(List.fold_left ladapt proof1 q1)
	(List.fold_left ladapt proof2 q2)
    | SClor (a, b, _, _), [l1; l2], 
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = 
	merge [List.remove_assoc a l1; List.remove_assoc b l2] in
      let q1 = replace l (List.remove_assoc a l1) in
      let q2 = replace l (List.remove_assoc b l2) in
      let c3 = unify c1 c2 in
      (eor (a, b), eor (List.assoc a l1, List.assoc b l2)) :: l,
      sclor (
	List.assoc a l1, List.assoc b l2, 
	radapt (List.fold_left ladapt proof1 q1) (c1, c3), 
	radapt (List.fold_left ladapt proof2 q2) (c2, c3))
    | SClimply (a, b, _, _), [l1; l2], 
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge [l1; List.remove_assoc b l2] in
      let b2 = List.assoc b l2 in
      let q1 = replace l l1 in
      let q2 = replace l (List.remove_assoc b l2) in
      (eimply (a, b), eimply (c1, List.assoc b l2)) :: l,
      sclimply (
	c1, b2, 
	List.fold_left ladapt proof1 q1, 
	List.fold_left ladapt proof2 q2)
    | SCrand (a, b, _, _), [l1; l2], 
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge [l1; l2] in
      let q1 = replace l l1 in
      let q2 = replace l l2 in
      l, scrand (
	c1, c2, 
	List.fold_left ladapt proof1 q1, 
	List.fold_left ladapt proof2 q2)
    | SClcontr (a, _), [l], [(g, c, _) as proof] ->
      (*eprintf "\nproblem with contraction\n";*)   
      let a1 = List.assoc a l in
      let a2 = List.assoc a (List.remove_assoc a l) in
      let a3 = unify 
	(List.assoc a l) 
	(List.assoc a (List.remove_assoc a l)) in
      (*p_debug "erfvrefv" [a1; a2; a3];
      let prooof = (ladapt proof (a2, a3)) in
      eprintf "\nproblem with contraction\n";*)
      (a, a3)
      :: List.remove_assoc a (List.remove_assoc a l),
      sclcontr (a3, ladapt (ladapt proof (a1, a3)) (a2, a3))
    | SCaxiom _, _, _ | SCfalse, _, _
    | SCtrue, _, _ | SCeqref _, _, _ | SCeqsym _, _, _
    | SCeqfunc _, _, _
      -> List.map (fun x -> (x, x)) lkg, lkproof
    | SCeqprop _, _ , _
      -> 
	List.map (fun x -> (x, x)) lkg, lkproof
    | SCrweak (a, _), [l], [(g, c, _) as proof] -> 
      l, scrweak (a, proof)
    | SCland (a, b, _), [l], [(g, c, _) as proof] ->
      (eand (a, b), eand (List.assoc a l,List.assoc b l))
      :: (List.remove_assoc a (List.remove_assoc b l)),
      scland (List.assoc a l, List.assoc b l, proof)
    | SClnot (e, _), [l], [(g, c, _) as proof] ->
      (enot e, enot c) :: l, sclnot (c, proof)
    | SCrorl (a, b, _), [l], [(g, c, _) as proof] ->
      l, scrorl (c, b, proof)
    | SCrorr (a, b, _), [l], [(g, c, _) as proof] ->
      l, scrorr (a, c, proof)
    | SCrimply (a, b, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc a l, scrimply (List.assoc a l, c, proof)
    | SCrnot (a, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc a l,
      scrnot (List.assoc a l, proof) 
    | SClall (Eall (x, ty, e, _) as ap, t, _), 
      [l], [(g, c, _) as proof] ->
      let h = eall (
	x, ty, 
	weaken e (List.assoc (substitute [(x, t)] e) l)) in
      (ap, h) :: (List.remove_assoc (substitute [(x, t)] e) l),
      sclall (h, t, proof)
    | SClex (Eex (x, ty, e, _) as ep, v, _), 
      [l], [(g, c, _) as proof] ->
      let h = eex (
	x, ty, 
	weaken e (List.assoc (substitute [(x, v)] e) l)) in
      (ep, h) :: (List.remove_assoc (substitute [(x, v)] e) l),
      sclex (h, v, proof)
    | SCrall (Eall (x, ty, e, _), v, _), [l], 
      [(g, c, _) as proof] ->
      l, scrall (eall (x, ty, weaken e c), v, proof)
    | SCrex (Eex (x, ty, e, _), t, _), [l], [(g, c, _) as proof] ->
      l, screx (eex (x, ty, weaken e c), t, proof)
    | SCcnot (e, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc (enot e) l, 
      scrnot (List.assoc (enot e) l, proof)
    | _, _, _ -> assert false in
  let ljg, _, _ = ljprf in
  assert (List.length lkg = List.length ljg);
  assert (List.length ljlist = List.length ljg);
  (*p_debug_proof "\nresult" ljprf;*)
  ljlist, ljprf
      
and newcut l aplus proof1 proof2 = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  if equal aplus c1 
  then
    l, sccut (aplus, proof1, proof2)
  else 
    match c1 with
    | Enot (Enot (c, _), _) when equal c aplus ->
      if equal c2 efalse
      then 
	l, sccut (
	  c1, proof1, 
	  sclnot (enot c, scrnot (c, proof2)))
      else
	l, sccut (
	  c1, proof1, 
	  scrnot (
	    enot c2, sclnot (
	      enot c, scrnot (
		c, sclnot (c2, proof2)))))
    | _ -> 
      p_debug "\nfail cut" [c1; aplus];
      assert false
	
and weaken ex et = 
  match ex, et with
  | Enot (Enot (fx, _), _), Enot (Enot (ft, _), _) -> 
    enot (enot (weaken fx ft))
  | _, Enot (Enot (ft, _), _) -> enot (enot (weaken ex ft))
  | Etrue, _ | Efalse, _
  | Evar _, _ | Eapp _, _-> ex
  | Eand (fx1, fx2, _), Eand (ft1, ft2, _) -> 
    eand (weaken fx1 ft1, weaken fx2 ft2)
  | Eor (fx1, fx2, _), Eor (ft1, ft2, _) -> 
    eor (weaken fx1 ft1, weaken fx2 ft2)
  | Eimply (fx1, fx2, _), Eimply (ft1, ft2, _) -> 
    eimply (weaken fx1 ft1, weaken fx2 ft2)
  | Enot (fx, _), Enot (ft, _) -> enot (weaken fx ft)
  | Eall (x, tyx, fx, _), Eall (y, _, ft, _) ->
    eall (x, tyx, weaken fx (substitute [(y, x)] ft))
  | Eex (x, tyx, fx, _), Eex (y, _, ft, _) ->
    eex (x, tyx, weaken fx (substitute [(y, x)] ft))
  | _, _ -> assert false

and merge assocs = 
  match assocs with
  | l1 :: l2 :: assocs ->
    let _,l = List.fold_left 
      (fun (q, r) (a, b) ->
	List.remove_assoc a q, (a, unify b (List.assoc a q)) :: r)
      (l1, []) l2 in
    merge (l :: assocs)
  | [l] -> l;
  | _ -> assert false;

and replace l1 l2 =
  let _, l = List.fold_left
    (fun (q, r) (a, b) -> 
      List.remove_assoc a q, (b, List.assoc a q) :: r)
    (l1, []) l2 in l

and unify e1 e2 =
  match e1, e2 with
  | Enot (Enot (f1, _), _), Enot (Enot (f2, _), _) -> 
    enot (enot (unify f1 f2))
  | Enot (Enot (f1, _), _), _ -> enot (enot (unify f1 e2))
  | _, Enot (Enot (f2, _), _) -> enot (enot (unify e1 f2))
  | Etrue, Etrue -> etrue
  | Efalse, Efalse -> efalse
  | Evar (x, _), Evar (y, _) when (x = y) -> evar (x)
  | Eapp (x, args1, _), Eapp (y, args2, _) 
    when (x = y && List.for_all2 equal args1 args2) -> 
    eapp (x, args1)
  | Eand (f1, f2, _), Eand (f3, f4, _) -> 
    eand (unify f1 f3, unify f2 f4)
  | Eor (f1, f2, _), Eor (f3, f4, _) -> 
    eor (unify f1 f3, unify f2 f4)
  | Eimply (f1, f2, _), Eimply (f3, f4, _) -> 
    eimply (unify f1 f3, unify f2 f4)
  | Enot (f1, _), Enot (f2, _) -> enot (unify f1 f2)
  | Eall (x, ty1, f1, _), Eall (y, _, f2, _) ->
    eall (x, ty1, unify f1 (substitute [(y, x)] f2))
  | Eex (x, ty1, f1, _), Eex (y, _, f2, _) ->
    eex (x, ty1, unify f1 (substitute [(y, x)] f2))
  | _, _ -> p_debug "fail unify" [e1; e2]; assert false

and adaptaxiom g e1 e2 =
  match e1, e2 with
  | Etrue, Etrue | Efalse, Efalse
  | Evar _, Evar _ | Eapp _, Eapp _ 
    -> scaxiom (e1, g)
  | Enot (f1, _), Enot (f2, _) -> 
    scrnot (
      f2, sclnot (
	f1, adaptaxiom g f2 f1))
  | Eand (f1, f2, _), Eand (f3, f4, _) -> 
    scland (f1, f2, scrand (
      f3, f4, 
      adaptaxiom (f2 :: g) f1 f3,
      adaptaxiom (f1 :: g) f2 f4))
  | Eor (f1, f2, _), Eor (f3, f4, _) -> 
    sclor (
      f1, f2, 
      scrorl (f3, f4, adaptaxiom g f1 f3),
      scrorr (f3, f4, adaptaxiom g f2 f4))
  | Eimply (f1, f2, _), Eimply (f3, f4, _) -> 
   scrimply (f3, f4, sclimply (
     f1, f2,
     adaptaxiom g f3 f1, 
     adaptaxiom (f3 :: g) f2 f4))
  | Eall (x, ty, f1, _), Eall (y, _, f2, _) ->
    let z = new_var () in
    scrall (
      e2, z, sclall (
	e1, z, adaptaxiom g 
	  (substitute [(x, z)] f1) 
	  (substitute [(y, z)] f2)))
  | Eex (x, ty, f1, _), Eex (y, _, f2, _) ->
    let z = new_var () in
    sclex (
      e1, z, screx (
	e2, z, adaptaxiom g
	  (substitute [(x, z)] f1) 
	  (substitute [(y, z)] f2)))
  | _, Enot (Enot (f2, _), _) ->
    scrnot (
      enot (f2), sclnot (
	f2, adaptaxiom g e1 f2))
  | _, _ -> assert false   

and ladapt proof (u, v) =
  (*p_debug "ladapt" [u; v];*)
  if equal u v then proof else
    let g, c, rule = proof in
    let result = match rule, v with
    | SClor (a, b, proof1, proof2), Eor (sa, sb, _) 
      when (equal u (eor (a, b))) -> 
      sclor (sa, sb, ladapt proof1 (a, sa), ladapt proof2 (b, sb))
    | SClimply (a, b, proof1, proof2), Eimply (sa, sb, _)
      when (equal u (eimply (a, b))) ->
      sclimply (
	sa, sb, radapt proof1 (a, sa), ladapt proof2 (b, sb))
    | SClcontr (a, proof), _ 
      when (equal a u) ->
      sclcontr (v, ladapt (ladapt proof (a, v)) (a, v))
    | SCland (a, b, proof), Eand (sa, sb, _) 
      when (equal u (eand (a, b))) ->
      scland (sa, sb, ladapt (ladapt proof (a, sa)) (b, sb))
    | SClnot (a, proof), Enot (sa, _) 
      when (equal u (enot a)) ->
      sclnot (sa, radapt proof (a, sa))
    | SClall (Eall (var, ty, e, _) as ap, t, proof), 
	Eall (svar, _, se, _) 
	  when (equal u ap) ->
      let z = substitute [(var, t)] e in
      let sz = substitute [(svar, t)] se in
      sclall (eall (svar, ty, se), t, ladapt proof (z, sz))
    | SClex (Eex (var, ty, e, _) as ep, v, proof), 
      Eex (svar, _, se, _) 
	when (equal u ep) ->
      let z = substitute [(var, v)] e in
      let sz = substitute [(svar, v)] se in
      sclex (eex (svar, ty, se), v, ladapt proof (z, sz))
    | SCaxiom (a), _ when equal u a -> adaptaxiom (rm u g) v u
    | SClnot _, _ | SClimply _, _ | SClor _, _ | SCland _, _
    | SClcontr _, _ | SCcut _, _ | SClex _, _ | SClall _, _ 
    | SCrweak _, _ | SCrnot _, _ | SCrand _, _ | SCrimply _, _ 
    | SCrorl _, _ | SCrorr _, _ | SCrall _, _ | SCrex _, _
      -> applytohyps (fun proof -> ladapt proof (u, v)) proof    
    | SCeqfunc _, _ | SCeqprop _, _ 
    | SCaxiom _, _ | SCfalse, _
    | SCtrue, _ | SCeqref _, _
    | SCeqsym _, _ -> v :: (rm u g), c, rule
    | SCcnot _, _ -> assert false in 
    let resultg, _, _ = result in
    assert (List.length resultg = List.length g);
    result

and radapt proof (a, b) =
  (*p_debug "radapt" [a; b];*)
  let rec xadapt proof (u, v) =
    let g, c, rule = proof in
    match rule, v with
    | SCcut (a, proof1, proof2), _ -> 
      sccut (a, proof1, radapt proof2 (u, v))
    | SClimply (a, b, proof1, proof2), _ ->
      sclimply (a, b, proof1, radapt proof2 (u, v)) 
    | SCrand (a, b, proof1, proof2), Eand (xa, xb, _) ->
      scrand (xa, xb, radapt proof1 (a, xa), radapt proof2 (b, xb))
    | SCrweak (a, proof), _ -> scrweak (v, proof)
    | SClnot (a, proof), _ -> sclnot (a, proof)
    | SCrorl (a, b, proof), Eor (xa, xb, _) ->
      scrorl (xa, xb, radapt proof (a, xa))
    | SCrorr (a, b, proof), Eor (xa, xb, _) ->
      scrorr (xa, xb, radapt proof (b, xb))
    | SCrimply (a, b, proof), Eimply (xa, xb, _) ->
      scrimply (xa, xb, radapt (ladapt proof (a, xa)) (b, xb))
    | SCrnot (a, proof), Enot (xa, _) ->
      scrnot (xa, ladapt proof (a, xa))
    | SCrall (Eall (var, ty, e, _), v, proof),
      Eall (xvar, _, xe, _) ->
      let z = substitute [(var, v)] e in
      let xz = substitute [(xvar, v)] xe in  
      scrall (eall (xvar, ty, xe), v, radapt proof (z, xz))
    | SCrex (Eex (var, ty, e, _), t, proof),
      Eex (xvar, _, xe, _) ->
      let z = substitute [(var, t)] e in
      let xz = substitute [(xvar, t)] xe in  
      screx (eex (xvar, ty, xe), t, radapt proof (z, xz))
    | SCtrue, _ | SCeqref _, _ | SCeqsym _, _      
    | SCeqfunc _, _ | SCeqprop _, _  -> proof
    | SCaxiom _, _ -> adaptaxiom (rm u g) u v
    | SCfalse, _ -> g, v, rule
    | SClcontr _, _ | SClor _, _ | SCland _, _
    | SClall _, _ | SClex _, _
      -> applytohyps (fun proof -> radapt proof (u, v)) proof 
    | SCcnot _, _ -> assert false
    | _, _ -> assert false in
  let rec headnots e1 e2 =
    match e1, e2 with
    | Enot (Enot (f1, _), _), Enot (Enot (f2, _), _) -> 
      headnots f1 f2
    | _, Enot (Enot (f2, _), _) -> true
    | _, _ -> false in
  if equal a b 
  then proof 
  else
    if headnots a b 
    then 
      match b with
      | Enot (Enot (e, _), _) -> 
	scrnot (enot (e), sclnot (e, radapt proof (a, e)))
      | _ -> assert false;
    else
      xadapt proof (a, b)

and rmnot proof =
  assert false;
;;

*and lltolkrule proof gamma =
  let hypslist, conclist = hypstoadd proof.rule in
  let newcontr, list = 
    List.fold_left (fun (cs, es) e -> 
      if (inlist e es) 
      then
	cs, rm e es
      else 
	e :: cs, es)
      ([], gamma) conclist in
  let contrshyps =
    List.map2 lltolkrule proof.hyps 
      (List.map (List.rev_append list) hypslist) in
  let contrs, prehyps = List.split contrshyps in
  let maincontr, remainders = union contrs in
  let hyps = List.map2 addhyp remainders prehyps in
  let preproof = xlltolkrule proof.rule hyps (maincontr@list) in
  (*p_debug "\ngamma" gamma;
  p_debug "\nconclist" conclist;
  List.iter (p_debug "hypslist") hypslist;
  p_debug "maincontr" maincontr;*)
  List.fold_left
    (fun (cs, prf) c -> 
      if inlist c conclist
      then cs, sclcontr (c, prf)
      else c :: cs, prf)
    (newcontr, preproof) maincontr*)

(*let rec rightsfromrule rule right =
  match rule, right with
  | Rfalse, _ -> []
  | Rnottrue, _ -> []
  | Raxiom (p), _ -> []
  | Rcut (p), [] -> [[]; []]
  | Rnoteq (a), _ -> []
  | Reqsym (a, b), _ -> []
  | Rnotnot (p) -> [[p]], [enot (enot p)], [[]]
  | Rconnect (b, p, q) -> 
    begin match b with
    | And -> [[p; q]], [eand (p, q)], [[]]
    | Or -> [[p]; [q]], [eor (p, q)], [[]; []]
    | Imply -> [[enot p]; [q]], [eimply (p, q)], [[enot p]; []]
    | Equiv -> assert false end
  | Rnotconnect (b, p, q) ->
    begin match b, bool with
    | And, false -> 
      [[enot p]; [enot q]], [enot (eand (p, q))], [[]; []]
    | And, true -> 
      [[enot p]; [enot q]], [enot (eand (p, q))], 
      [[enot p]; [enot q]]
    | Or, false -> 
      [[enot p; enot q]], [enot (eor (p, q))], [[]]
    | Or, true -> 
      [[enot p; enot q]], [enot (eor (p, q))], [[enot p; enot q]]
    | Imply, false -> 
      [[p; enot q]], [enot (eimply (p, q))], [[]] 
    | Imply, true -> 
      [[p; enot q]], [enot (eimply (p, q))], [[enot q]]
    | Equiv, _ -> assert false end
  | Rex (ep, v) -> 
    begin match ep with
    | Eex (x, ty, p, _) -> [[substitute [(x, v)] p]], [ep], []
    | _ -> assert false end
  | Rall (ap, t) -> 
    begin match ap with
    | Eall (x, ty, p, _) -> [[substitute [(x, t)] p]], [ap], []
    | _ -> assert false end
  | Rnotex (ep, t) -> 
    begin match ep with
    | Eex (x, ty, p, _) -> 
      [[enot (substitute [(x, t)] p)]], [enot ep]
    | _ -> assert false end
  | Rnotall (ap, v) -> 
    begin match ap with
    | Eall (x, ty, p, _) -> 
      [[enot (substitute [(x, v)] p)]], [enot ap]
    | _ -> assert false end
  | Rpnotp (e1, e2) -> 
    begin match e1, e2 with
    | Eapp (p, ts, _), Enot (Eapp (q, us, _), _) ->
      List.map2 
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us, 
      [e1; e2]
    | _ -> assert false end
  | Rnotequal (e1, e2) -> 
    begin match e1, e2 with
    | Eapp (p, ts, _), Eapp (q, us, _) ->
      List.map2 
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us, 
      [enot (eapp ("=", [e1; e2]))]
    | _ -> assert false end
  | RcongruenceLR (p, a, b) -> 
    [[apply p b]], [apply p a; eapp ("=", [a; b])]
  | RcongruenceRL (p, a, b) -> 
    [[apply p b]], [apply p a; eapp ("=", [b; a])]
  | Rextension (ext, name, args, concs, hyps) ->
    hyps, concs
  | Rlemma (name, args) ->
    assert false;
  | _ -> assert false*)

    (*eprintf "%d, %d\n" (List.length l1 + List.length g)  
      (List.length l2 + List.length g2);*)
