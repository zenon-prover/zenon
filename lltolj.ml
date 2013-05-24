open Printf;;
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

type lkrule =
| SCaxiom of expr
| SClfalse
| SCtrue
| SCeqref of expr
| SCeqsym of expr * expr
| SCeqprop of expr * expr * lkproof list
| SCeqfunc of expr * expr * lkproof list
| SCrfalse of expr * lkproof
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
let sclfalse (g, e) = efalse :: g, e, SClfalse;;
let sctrue (g) = g, etrue, SCtrue;;
let sceqref (a, g) = g, eapp ("=", [a; a]), SCeqref (a);;
let sceqsym (a, b, g) =
  eapp ("=", [a; b]) :: g, eapp ("=", [b; a]), SCeqsym (a, b);;
let sceqprop (e1, e2, proofs) =
  match proofs with
  | [] -> [e1], e2, SCeqprop (e1, e2, [])
  | (g, c, rule) as proof :: proofs ->
    match e1, e2 with
    | Eapp (x, t :: ts, _), Eapp (y, u :: us, _) ->
      e1 :: g, e2, SCeqprop (e1, e2, proof :: proofs)
    | _ -> assert false;;
let sceqfunc (e1, e2, proofs) =
  match proofs with
  | [] -> [e1], e2, SCeqprop (e1, e2, [])
  | (g, c, rule) as proof :: proofs ->
    match e1, e2 with
    | Eapp (x, t :: ts, _), Eapp (y, u :: us, _) ->
      e1 :: g, e2, SCeqfunc (e1, e2, proof :: proofs)
    | _ -> assert false;;
let scrfalse (e, proof) =
  let g, c, rule = proof in
  assert (equal c efalse);
  g, e, SCrfalse (e, proof);;
let sclcontr (e, proof) =
  let g, c, rule = proof in
  assert (List.mem e g);
  assert (List.mem e (rm e g));
  rm e g, c, SClcontr (e, proof)
let sccut (e, proof1, proof2) = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  g1, c2, SCcut(e, proof1, proof2);;
let scland (e1, e2, proof) = 
  assert (ingamma e2 proof);
  let (g, c, rule) = proof in
  assert (List.mem e1 (rm e2 g));
  (eand (e1, e2)) :: rm e1 (rm e2 g), c, SCland (e1, e2, proof);;
let sclor (e1, e2, proof1, proof2) = 
  assert (ingamma e1 proof1);
  let (g1, c, rule1) = proof1 in
  (eor (e1, e2)) :: rm e1 g1, c, SClor (e1, e2, proof1, proof2);;
let sclimply (e1, e2, proof1, proof2) = 
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  (eimply (e1, e2)) :: g1, c2, 
  SClimply (e1, e2, proof1, proof2);;
let sclnot (e, f, proof) = 
  let (g, d, rule) = proof in
  (enot e) :: g, f, SClnot (e, proof);;
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
let sccnot (e, proof) =
  let (g, c, rule) = proof in
  assert (List.mem (enot e) g);
  assert (equal c efalse);
  rm (enot e) g, e, SCcnot (e, proof);;

let scconc (g, c, rule) = c;;

let lemma_env = 
  (Hashtbl.create 97 : (string, prooftree) Hashtbl.t)
;;

let hypothesis_env = ref [];;

let definition_env =
  (Hashtbl.create 97 : (string, expr list * expr) Hashtbl.t)
;;

let new_terms = ref [];;

let hypsofrule lkrule =
  match lkrule with
  | SCaxiom (e) -> []
  | SClfalse -> []
  | SCtrue -> []
  | SCeqref (e) -> []
  | SCeqsym (e1, e2) -> []
  | SCeqprop (e1, e2, proofs) -> proofs
  | SCeqfunc (e1, e2, proofs) -> proofs
  | SCrfalse (e, proof) -> [proof]
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
  | SClfalse -> g, c, SClfalse
  | SCtrue -> g, c, SCtrue
  | SCeqref (e) -> g, c, SCeqref (e)
  | SCeqsym (e1, e2) -> g, c, SCeqsym (e1, e2)
  | SCeqprop (e1, e2, proofs) -> 
    sceqprop (e1, e2, List.map f proofs)
  | SCeqfunc (e1, e2, proofs) -> 
    sceqfunc (e1, e2, List.map f proofs)
  | SCrfalse (e, proof) -> scrfalse (e, f proof)
  | SClcontr (e, proof) -> sclcontr (e, f proof)
  | SCcut (e, proof1, proof2) -> 
    sccut (e, f proof1, f proof2)
  | SCland (e1, e2, proof) ->
    scland (e1, e2, f proof)
  | SClor (e1, e2, proof1, proof2) ->
    sclor (e1, e2, f proof1, f proof2)
  | SClimply (e1, e2, proof1, proof2) ->
    sclimply (e1, e2, f proof1, f proof2)
  | SClnot (e, proof) -> sclnot (e, c, f proof)
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

let rec rmtau tau z e = 
  if equal e tau
  then z 
  else
    match e with
    | Emeta _ | Evar _ | Etau _ 
    | Elam _ | Etrue | Efalse -> e
    | Eapp (s, args, _) ->
      eapp (s, List.map (rmtau tau z) args)
    | Enot (e, _) ->
      enot (rmtau tau z e)
    | Eand (e1, e2, _) ->
      eand (rmtau tau z e1, rmtau tau z e2)
    | Eor (e1, e2, _) ->
      eor (rmtau tau z e1, rmtau tau z e2)
    | Eimply (e1, e2, _) ->
      eimply (rmtau tau z e1, rmtau tau z e2)
    | Eequiv (e1, e2, _) ->
      eequiv (rmtau tau z e1, rmtau tau z e2)
    | Eall (x, s, e, _) ->
      eall (x, s, rmtau tau z e)
    | Eex (x, s, e, _) ->
      eex (x, s, rmtau tau z e)
;;

let rec rmtau_proof tau z (g, c, rule) = 
    match rule with 
    | SCaxiom (e) -> 
      List.map (rmtau tau z) g, rmtau tau z c, 
      SCaxiom (rmtau tau z e)
    | SClfalse -> 
      List.map (rmtau tau z) g, rmtau tau z c,
      SClfalse
    | SCtrue -> 
      List.map (rmtau tau z) g, rmtau tau z c, 
      SCtrue
    | SCeqref (e) -> 
      List.map (rmtau tau z) g, rmtau tau z c, 
      SCeqref (rmtau tau z e)
    | SCeqsym (e1, e2) -> 
      List.map (rmtau tau z) g, rmtau tau z c, 
      SCeqsym (rmtau tau z e1, rmtau tau z e2)
    | SCeqprop (e1, e2, proofs) -> 
      sceqprop (
	rmtau tau z e1, rmtau tau z e2, 
	List.map (rmtau_proof tau z) proofs)
    | SCeqfunc (e1, e2, proofs) -> 
      sceqfunc (
	rmtau tau z e1, rmtau tau z e2, 
	List.map (rmtau_proof tau z) proofs)
    | SCrfalse (e, proof) -> 
      scrfalse (rmtau tau z e, (rmtau_proof tau z) proof)
    | SClcontr (e, proof) -> 
      sclcontr (rmtau tau z e, (rmtau_proof tau z) proof)
    | SCcut (e, proof1, proof2) -> 
      sccut (
	rmtau tau z e, 
	(rmtau_proof tau z) proof1, (rmtau_proof tau z) proof2)
    | SCland (e1, e2, proof) ->
      scland (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SClor (e1, e2, proof1, proof2) ->
      sclor (
	rmtau tau z e1, rmtau tau z e2, 
	(rmtau_proof tau z) proof1, (rmtau_proof tau z) proof2)
    | SClimply (e1, e2, proof1, proof2) ->
      sclimply (
	rmtau tau z e1, rmtau tau z e2, 
	(rmtau_proof tau z) proof1, (rmtau_proof tau z) proof2)
    | SClnot (e, proof) -> 
      sclnot (
	rmtau tau z e, rmtau tau z c, (rmtau_proof tau z) proof)
    | SClall (e1, e2, proof) -> 
      sclall (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SClex (e1, e2, proof) -> 
      sclex (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SCrand (e1, e2, proof1, proof2) ->
      scrand (
	rmtau tau z e1, rmtau tau z e2, 
	(rmtau_proof tau z) proof1, (rmtau_proof tau z) proof2)
    | SCrorl (e1, e2, proof) -> 
      scrorl (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SCrorr (e1, e2, proof) ->
      scrorr (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SCrimply (e1, e2, proof) ->
      scrimply (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SCrnot (e, proof) -> scrnot (
      rmtau tau z e, (rmtau_proof tau z) proof)
    | SCrall (e1, e2, proof) -> 
      scrall (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SCrex (e1, e2, proof) -> 
      screx (
	rmtau tau z e1, rmtau tau z e2, (rmtau_proof tau z) proof)
    | SCcnot (e, proof) -> 
      sccnot (rmtau tau z e, (rmtau_proof tau z) proof)
;;

let rec xaddhyp h lkproof =
  let g, c, lkrule = lkproof in 
  match lkrule with
  | SCaxiom _ | SClfalse 
  | SCtrue | SCeqref _ | SCeqsym _ -> 
    h :: g, c, lkrule
  | _ -> applytohyps (xaddhyp h) lkproof
    
and rmhyps hyps g = 
  match hyps with
  | h :: hs when List.mem h g -> rmhyps hs (rm h g)
  | h :: hs -> h :: rmhyps hs g
  | [] -> []
    
and addhyp hyps lkproof =
  let g, c, lkrule = lkproof in
  List.fold_left (fun pf h -> xaddhyp h pf) lkproof (rmhyps hyps g)
;;  

let rec use_defs e = 
  match e with
  | Evar (v, _) when Hashtbl.mem definition_env v -> 
    let (params, body) = Hashtbl.find definition_env v in
    body
  | Eapp (s, args, _) when Hashtbl.mem definition_env s ->
    let exprs = List.map use_defs args in
    let (params, body) = Hashtbl.find definition_env s in
    substitute (List.combine params exprs) body
  | Evar (_, _) | Etrue | Efalse -> e
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
    etau (x, s, use_defs e)
  | Elam (x, s, e, _) ->
    elam (x, s, use_defs e)
  | Emeta _ -> 
    assert false

and use_defs_rule rule =
  match rule with
  | Rfalse -> Rfalse
  | Rnottrue -> Rnottrue
  | Raxiom (p) -> Raxiom (use_defs p)
  | Rcut (p) -> Rcut (use_defs p)
  | Rnoteq (a) -> Rnoteq (a)
  | Reqsym (a, b) -> Reqsym (a, b)
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
  | Rlemma (name, args) -> rule
  | RcongruenceLR (p, a, b) -> 
    RcongruenceLR (use_defs p, use_defs a, use_defs b)
  | RcongruenceRL (p, a, b) -> 
    RcongruenceRL (use_defs p, use_defs a, use_defs b)
;;

let rec union lists = 
  match lists with
  | [] -> [], []
  | [list] -> list, [[]]
  | [] :: lists -> 
    let main, remainders = union lists in
    main, main :: remainders
  | (x :: l) :: lists ->
    let main, remainders = union lists in
    match remainders with
    | remainder :: remainders ->
      if List.mem x main 
      then 
	if List.mem x remainder
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
    | Equiv -> [[enot p; enot q]; [p; q]], [eequiv (p, q)]  end
  | Rnotconnect (b, p, q) -> 
    begin match b with
    | And -> [[enot p]; [enot q]], [enot (eand (p, q))]
    | Or -> [[enot p; enot q]], [enot (eor (p, q))]
    | Imply -> [[p; enot q]], [enot (eimply (p, q))]
    | Equiv -> 
      [[enot p; q]; [p; enot q]], [enot (eequiv (p, q))]  end
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
    let g, d, rule = lltolk (Hashtbl.find lemma_env name) None in
    [], g
  | _ -> assert false

and lltolk proof goal =
  let pregamma = 
    match goal with
    | Some (Enot (g, _)) -> enot g :: !hypothesis_env
    | None -> !hypothesis_env
    | _ -> assert false in
  let gamma = List.map use_defs pregamma in
  let l, lkproof = lltolkrule proof gamma in
  assert (l = []);
  lkproof

and righttoleft e proof =
  sclnot (e, efalse, proof)

and lefttoright e proof =
  match e with
  | Enot (f, _) -> optimize (scrnot (f, rmdblnot f proof))
  | _ -> 
    let g, c, rule = proof in
    let ne = enot e in
    assert (equal c efalse);
    assert (ingamma ne proof);
    match rule with
    | SClnot (f, prf) when (equal f e) -> prf
    | SClcontr (f, _) when (equal ne f) -> sccnot (e, proof)
      
    | SClcontr _
    | SClor _ | SCland _
    | SClex _ | SClall _ 
      -> applytohyps (lefttoright e) proof
      
    | _ -> sccnot (e, proof)
      
and rmdblnot e proof =  
  let g, c, rule = proof in
  match rule with
  | SClnot (Enot (f, _), proof) when equal f e ->
    xrmdblnot e proof
  | SCaxiom (Enot (Enot (f, _), _)) when equal f e ->
    scrnot (
      enot e, sclnot (
	e, efalse, scaxiom (e, rm (enot (enot e)) g)))
  | SClfalse -> sclfalse (e :: rm (enot (enot e)) g, c)
  | SCtrue -> sctrue (e :: rm (enot (enot e)) g)
  | SCeqref (a) -> sceqref (a, e :: rm (enot (enot e)) g)
  | SCeqsym (a, b) -> sceqsym (a, b, e :: rm (enot (enot e)) g)
  | SClcontr (Enot (Enot (f, _), _), proof) when equal f e ->
    rmdblnot e (rmdblnot e proof)
  | _ -> applytohyps (rmdblnot e) proof

and xrmdblnot e proof =
  let g, c, rule = proof in
  match rule with
  | SCaxiom (Enot (f, _)) when equal f e ->
    sclnot (f, efalse, scaxiom (f, rm (enot f) g))
  | _ -> assert false;

and optimize proof =
  let g, c, rule = proof in
  match rule with
  | SCcnot (e, proof) -> lefttoright e proof
  | _ -> applytohyps optimize proof
    
and lltolkrule proof gamma =
  let rule = use_defs_rule proof.rule in 
  (*is use_defs_rule necessary ?*)
  let prehypslist, preconclist = hypstoadd rule in
  let hypslist = List.map (List.map use_defs) prehypslist in
  let conclist = List.map use_defs preconclist in
  let newcontr, list = 
    List.fold_left (fun (cs, es) e -> 
      if (List.mem e es) 
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
  let preproof = (xlltolkrule rule hyps (maincontr@list)) in
  (*p_debug "\nconclist" conclist;
  p_debug "gamma" gamma;
  List.iter (p_debug "hypslist") hypslist;
  p_debug "maincontr" maincontr;*)
  List.fold_left 
    (fun (cs, prf) c -> 
      if List.mem c conclist 
      then cs, sclcontr (c, prf) 
      else c :: cs, prf)
    (newcontr, preproof) maincontr

and xlltolkrule rule hyps gamma =
  match rule, hyps with
  | Rfalse, [] ->
    sclfalse (gamma, efalse)
  | Rnottrue, [] ->
    righttoleft etrue (sctrue (gamma))
  | Raxiom (p), [] -> 
    righttoleft p (scaxiom (p, gamma))
  | Rcut (p), [proof1; proof2] -> 
    assert (ingamma p proof2);
    sccut (p, lefttoright p proof2, proof1)
  | Rnoteq (a), [] -> 
    righttoleft (eapp ("=", [a; a])) (sceqref (a, gamma));
  | Reqsym (a, b), [] ->
    righttoleft (eapp ("=", [b; a]))
      (sceqsym (a, b, gamma))
  | Rnotnot (p), [proof] ->
    righttoleft (enot (p))
      (scrnot (p, proof))
  | Rconnect (And, p, q), [proof] ->
    scland (p, q, proof)
  | Rconnect (Or, p, q), [proof1; proof2] ->
    sclor (p, q, proof1, proof2)
  | Rconnect (Imply, p, q), [proof1; proof2] ->
    assert (ingamma (enot p) proof1);
    sclimply (p, q, lefttoright p proof1, proof2)
  | Rconnect (Equiv, p, q), [proof1; proof2] ->
    assert (ingamma (enot q) proof1);
    assert (ingamma (enot p) (sclimply (
      q, p, 
      lefttoright q proof1, 
      sclnot (p, efalse, scaxiom (p, gamma)))));
    scland (
      eimply (p, q), eimply (q, p),
      sclimply (
	p, q,
	lefttoright p 
	  (sclimply (
	    q, p, 
	    lefttoright q proof1, 
	    sclnot (p, efalse, scaxiom (p, gamma)))),
	sclimply (
	  q, p,
	  scaxiom (q, gamma), proof2)))
  | Rnotconnect (And, p, q), [proof1; proof2] ->
    assert (ingamma (enot p) proof1);
    assert (ingamma (enot q) proof2);
    righttoleft (eand (p, q))
      (scrand (p, q, lefttoright p proof1, lefttoright q proof2))
  | Rnotconnect (Or, p, q), [proof] ->
    assert (ingamma (enot q) proof);
    assert (ingamma (enot p)
	      (righttoleft (eor (p, q)) (
		scrorr (
		  p, q, 
		  lefttoright q proof))));
    begin match q with
    | Enot _ ->
      sclcontr (
	enot (eor (p, q)), 
	righttoleft (eor (p, q)) (
	  scrorr (
	    p, q, 
	    lefttoright q (
	      righttoleft (eor (p, q)) (
		scrorl (
		  p, q, 
		  lefttoright p proof))))))
    | _ -> 
      sclcontr (
	enot (eor (p, q)), 
	righttoleft (eor (p, q)) (
	  scrorl (
	    p, q, 
	    lefttoright p (
	      righttoleft (eor (p, q)) (
		scrorr (
		  p, q, 
		  lefttoright q proof)))))) end
  | Rnotconnect (Imply, p, q), [proof] ->
    assert (ingamma (enot q) proof); 
    righttoleft (eimply (p, q))
      (scrimply (p, q, lefttoright q proof))
  | Rnotconnect (Equiv, p, q), [proof1; proof2] ->
    assert (ingamma (enot q) proof2);
    assert (ingamma (enot p) proof1);
    righttoleft (eand (eimply (p, q), eimply (q, p)))
      (scrand (eimply (p, q), eimply (q, p), 
	       scrimply (p, q, lefttoright q proof2),
	       scrimply (q, p, lefttoright p proof1)))
  | Rex (ep, v), [proof] ->
    let z = new_var () in
    new_terms := z :: !new_terms;
    sclex (ep, z, rmtau_proof v z proof)
  | Rall (ap, t), [proof] ->
    sclall (ap, t, proof)
  | Rnotex (Eex(x, ty, p, _) as ep, t), [proof] ->
    assert (ingamma (enot (substitute [(x, t)] p)) proof);
    righttoleft ep
      (screx (ep, t, lefttoright (substitute [(x, t)] p) proof))
  | Rnotall (Eall(x, ty, p, _) as ap, v), [proof] ->
    assert (ingamma (enot (substitute [(x, v)] p)) proof);
    let z = new_var () in
    new_terms := z :: !new_terms;
    righttoleft ap (
      scrall (
	ap, z, 
	lefttoright (substitute [(x, z)] p) 
	  (rmtau_proof v z proof)))
  | Rpnotp (Eapp (p, ts, _), Enot (Eapp (q, us, _), _)), proofs ->
    righttoleft (eapp (q, us))
      (sceqprop (
	eapp (p, ts), eapp (q, us), 
	List.map2 lefttoright 
	  (List.map2 
	     (fun t u -> eapp ("=", [t; u])) ts us) proofs))
  | Rnotequal (Eapp (f, ts, _), Eapp (g, us, _)), 
    proofs ->
    righttoleft (eapp ("=", [eapp (f, ts); eapp (g, us)]))
      (sceqfunc (
	eapp (f, ts), eapp (g, us), 
	List.map2 lefttoright 
	  (List.map2 
	     (fun t u -> eapp ("=", [t; u])) ts us) proofs))
  | RcongruenceLR (p, a, b), [proof] ->
    let g, c, rule = proof in
    begin match p with
    | Elam (x, ty, e, _) -> 
      sccut (
	apply p b, 
	addhyp (rm (apply p b) g) (rmcongruence true x e a b), 
	addhyp [apply p a; eapp ("=", [a; b])] proof)
    | _ -> assert false end
  | RcongruenceRL (p, a, b), [proof] ->
    let g, c, rule = proof in
    begin match p with
    | Elam (x, ty, e, _) ->
      sccut (
	apply p b, 
	addhyp (rm (apply p b) g) (rmcongruence false x e a b), 
	addhyp [apply p a; eapp ("=", [a; b])] proof)
    | _ -> assert false end  
  | Rdefinition (name, sym, args, body, recarg, fld, unf), [proof] 
    -> proof
  | Rextension (
    "", "zenon_notallex", [Elam (v, t, p, _)], 
    [Enot (Eall (x, s, e, _) as ap, _)], [[ep]]), [proof] ->
    let z = new_var () in
    new_terms := z :: !new_terms;
    let tau = etau (x, s, enot e) in
    let q = substitute [(v, z)] p in
    assert (ingamma (enot q) (
	  sccut (
	    ep,
	    screx (
	      ep, z, scaxiom (
		enot q, List.map (rmtau tau z) gamma)),
	    addhyp [enot q] (rmtau_proof tau z proof))));
    righttoleft (ap)
      (scrall (
	ap, z, lefttoright q (
	  sccut (
	    ep,
	    screx (
	      ep, z, scaxiom (
		enot q, List.map (rmtau tau z) gamma)),
	    addhyp [enot q] (rmtau_proof tau z proof)))))
  | Rextension (ext, name, args, cons, hyps), proofs -> 
    assert false
  | Rlemma (name, args), [] -> 
    let proof = Hashtbl.find lemma_env name in
    lltolk proof None
  | _ -> assert false

and rmcongruence s x e a b =
  match e with
  | Etrue | Efalse | Evar _ | Etau _ -> scaxiom (e, [])
  | Eapp (f, args, _) -> 
    sceqprop (
      substitute [(x, a)] e, substitute [(x, b)] e, 
    List.map (fun t -> xrmcongruence s x t a b) args)
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
	rmcongruence (not s) x e1 a b,
	addhyp [substitute [(x, b)] e1] (rmcongruence s x e2 a b)))
  | Enot (e0, _) -> 
    scrnot (
      substitute [(x, b)] e0,
      sclnot (
	substitute [(x, a)] e0, efalse,
	rmcongruence (not s) x e0 a b))
  | Eall (y, ty, e0, _) ->
    scrall (
      substitute [(x, b)] e, 
      substitute [(x, b)] (etau (y, ty, enot e0)),
      sclall (
	substitute [(x, a)] e, 
	substitute [(x, a)] (etau (y, ty, enot e0)),
	rmcongruence s x 
	  (substitute [(y, etau (y, ty, enot e0))] e0) a b))
  | Eex (y, ty, e0, _) ->
    screx (
      substitute [(x, b)] e, 
      substitute [(x, b)] (etau (y, ty, e0)),
      sclex (
	substitute [(x, a)] e, 
	substitute [(x, a)] (etau (y, ty, e0)),
	rmcongruence s x 
	  (substitute [(y, etau (y, ty, e0))] e0) a b))
  | Elam _ | Emeta _ | Eequiv _ ->
    assert false
      
and xrmcongruence s x t a b =
  match t with
  | Evar (v, _) when (equal x t) -> 
    if s
    then scaxiom (eapp ("=", [a; b]), []) 
    else sceqsym (b, a, [])
  | Evar _ | Etau _ -> sceqref (t, [])
  | Eapp (f, args, _) -> 
    sceqfunc (
      substitute [(x, a)] t, substitute [(x, b)] t, 
      List.map (fun t -> xrmcongruence s x t a b) args) 
  | _ -> assert false   
;;

let rec lltolj proof goal =
  let result = match goal with 
    | Some (Enot (g, _)) -> 
      let newgoal = use_defs g in
      (*let ga, _, _ = lltolk proof goal in
      assert (List.mem (enot newgoal) ga);*)
      newgoal, lefttoright newgoal (lltolk proof goal)
    | None ->
      efalse, lltolk proof goal;
    | _ -> assert false in
  let conc, lkproof = List.fold_left
    (fun (conc, rule) stmt ->
      let newstmt = use_defs stmt in
      eimply (newstmt, conc), 
      scrimply (newstmt, conc, addhyp [newstmt] rule)
    )
    result !hypothesis_env in
  let _, ljproof = lltoljrule lkproof in
  !new_terms, ljproof
    
and lltoljrule lkproof =
  p_debug_proof "seq" lkproof;
  let lkg, lkc, rule = lkproof in
  let assocs, proofs =
    List.split (List.map lltoljrule (hypsofrule rule)) in
  let ljlist, ljprf =
  match rule, assocs, proofs with
    | SCcut (a, _, _), [l1; l2],
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge [l1; List.remove_assoc a l2] in
      let q1 = replace l l1 in
      let q2 = replace l (List.remove_assoc a l2) in
      newcut l (List.assoc a l2)
	(List.fold_left ladapt proof1 q1)
	(List.fold_left ladapt proof2 q2)
      (*let l3, proof3 = 
	lmodify l2 proof2 ((List.assoc a l2), c1) in
      let l = merge [l1; List.remove_assoc a l3] in
      let q1 = replace l l1 in
      let q3 = replace l (List.remove_assoc a l3) in
      l, sccut (
	c1, 
	List.fold_left ladapt proof1 q1, 
	List.fold_left ladapt proof3 q3)*)
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
    | SCeqprop (e1, e2, _), _ , _ -> 
      let ljproofs = List.map rmnot proofs in
      let l = merge assocs in
      let qs = List.map (replace l) assocs in
      l, sceqprop (
	e1, e2, List.map2 (List.fold_left ladapt) ljproofs qs)
    | SCeqfunc (e1, e2, _), _, _ ->
      let ljproofs = List.map rmnot proofs in
      let l = merge assocs in
      let qs = List.map (replace l) assocs in
      (e1, e1) :: l, sceqfunc (
	e1, e2, List.map2 (List.fold_left ladapt) ljproofs qs)
    | SCcnot (e, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc (enot e) l,
      scrnot (List.assoc (enot e) l, proof)
    | SClcontr (a, _), [l], [(g, c, _) as proof] ->
      let a1 = List.assoc a l in
      let a2 = List.assoc a (List.remove_assoc a l) in
      let a3 = unify 
	(List.assoc a l) 
	(List.assoc a (List.remove_assoc a l)) in
      p_debug "fail" [a1; a2; a3];
      p_debug_proof "with1" (ladapt proof (a1, a3));
      p_debug_proof "with2" 
	(ladapt (ladapt proof (a1, a3)) (a2, a3));
      (a, a3)
      :: List.remove_assoc a (List.remove_assoc a l),
      sclcontr (a3, ladapt (ladapt proof (a1, a3)) (a2, a3))
    | SCaxiom _, _, _ | SClfalse, _, _
    | SCtrue, _, _ | SCeqref _, _, _ | SCeqsym _, _, _
      -> List.map (fun x -> (x, x)) lkg, lkproof
    | SCrfalse (a, _), [l], [(g, c, _) as proof] -> 
      List.remove_assoc a l, scrfalse (a, proof)
    | SCland (a, b, _), [l], [(g, c, _) as proof] ->
      (eand (a, b), eand (List.assoc a l,List.assoc b l))
      :: (List.remove_assoc a (List.remove_assoc b l)),
      scland (List.assoc a l, List.assoc b l, proof)
    | SClnot (e, _), [l], [(g, c, _) as proof] ->
      (enot e, enot c) :: l, sclnot (c, lkc, proof)
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
    | _, _, _ -> assert false in
  p_debug_proof "result" ljprf; 
  ljlist, ljprf

      
and newcut l aplus proof1 proof2 = 
  let (g1, c1, rule1) = proof1 in
  if equal aplus c1 
  then
    l, sccut (aplus, proof1, proof2)
  else 
    assert false;

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
  | _, _ -> assert false

and adaptaxiom g e1 e2 =
  match e1, e2 with
  | Etrue, Etrue | Efalse, Efalse
  | Evar _, Evar _ | Eapp _, Eapp _ 
    -> scaxiom (e1, g)
  | Enot (f1, _), Enot (f2, _) -> 
    scrnot (
      f2, sclnot (
	f1, efalse, adaptaxiom g f2 f1))
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
     adaptaxiom g f1 f3, 
     adaptaxiom (f1 :: g) f2 f4))
  | Eall (x, ty, f1, _), Eall (y, _, f2, _) ->
    let t = etau (x, ty, enot (f2)) in
    scrall (
      e2, t, sclall (
	e1, t, adaptaxiom g 
	  (substitute [(x, t)] f1) 
	  (substitute [(y, t)] f2)))
  | Eex (x, ty, f1, _), Eex (y, _, f2, _) ->
    let t = etau (x, ty, f1) in
    screx (
      e2, t, sclex (
	e1, t, adaptaxiom g
	  (substitute [(x, t)] f1) 
	  (substitute [(y, t)] f2)))
  | _, Enot (Enot (f2, _), _) ->
    scrnot (
      enot (f2), sclnot (
	f2, efalse, adaptaxiom g e1 f2))
  | _, _ -> assert false    

and ladapt proof (u, v) =
  let g, c, rule = proof in
  match rule, v with
  | SClor (a, b, proof1, proof2), Eor (sa, sb, _) 
    when (equal u (eor (a, b))) -> 
    sclor (sa, sb, ladapt proof1 (a, sa), ladapt proof2 (b, sb))
  | SClimply (a, b, proof1, proof2), Eimply (sa, sb, _)
    when (equal u (eimply (a, b))) ->
    sclimply (sa, sb, radapt proof1 (a, sa), ladapt proof2 (b, sb))
  | SClcontr (a, proof), _ 
    when (equal a u) ->
    sclcontr (v, ladapt (ladapt proof (a, v)) (a, v))
  | SCaxiom (a), _ 
    when (equal a u) -> adaptaxiom (rm u g) v u
  | SCland (a, b, proof), Eand (sa, sb, _) 
    when (equal u (eand (a, b))) ->
    scland (sa, sb, ladapt (ladapt proof (a, sa)) (b, sb))
  | SClnot (a, proof), Enot (sa, _) 
    when (equal u (enot a)) ->
    sclnot (sa, c, radapt proof (a, sa))
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
  | SClnot _, _ | SClimply _, _ | SClor _, _ | SCland _, _
  | SCeqfunc _, _ | SCeqprop _, _ 
  | SClcontr _, _ | SCcnot _, _ | SCcut _, _
  | SClex _, _ | SClall _, _ 
  | SCrfalse _, _ | SCrnot _, _ | SCrand _, _ | SCrimply _, _ 
  | SCrorl _, _ | SCrorr _, _ | SCrall _, _ | SCrex _, _
    -> p_debug "cpl" [u; v] ; applytohyps (fun proof -> ladapt proof (u, v)) proof    
  | SCaxiom (a), _ -> scaxiom (a, v :: (rm u (rm a g)))
  | SClfalse, _ -> sclfalse (v :: (rm u g), c)
  | SCtrue, _ -> sctrue (v :: (rm u g))
  | SCeqref (a), _ -> sceqref (a, v :: (rm u g))
  | SCeqsym (a, b), _ -> sceqsym (a, b, v :: (rm u g))

and radapt proof (a, b) =
p_debug "rcpl" [a; b] ;
  let rec xadapt proof (u, v) =
    let g, c, rule = proof in
    match rule, v with
    | SCcut (a, proof1, proof2), _ -> 
      sccut (a, proof1, radapt proof2 (u, v))
    | SClimply (a, b, proof1, proof2), _ ->
      sclimply (a, b, proof1, radapt proof2 (u, v)) 
    | SCrand (a, b, proof1, proof2), Eand (xa, xb, _) ->
      scrand (xa, xb, radapt proof1 (a, xa), radapt proof2 (b, xb))
    | SCcnot (a, proof), _ ->
      sccnot (v, ladapt proof (enot u, enot v))
    | SCrfalse (a, proof), _ -> scrfalse (v, proof)
    | SClnot (a, proof), _ -> sclnot (a, v, proof)
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
    | SClfalse, _ -> sclfalse (g, v)
    | SClcontr _, _ | SClor _, _ | SCland _, _
    | SClall _, _ | SClex _, _
      -> applytohyps (fun proof -> radapt proof (u, v)) proof 
    | _, _ -> assert false in
  let rec headnots e1 e2 =
  match e1, e2 with
  | Enot (Enot (f1, _), _), Enot (Enot (f2, _), _) -> 
    headnots f1 f2
  | _, Enot (Enot (f2, _), _) -> true
  | _, _ -> false in
  if headnots a b 
  then 
    match b with
    | Enot (Enot (e, _), _) -> 
      scrnot (enot (e), sclnot (e, efalse, radapt proof (a, e)))
    | _ -> assert false;
  else
    xadapt proof (a, b)

and rmnot proof =
  assert false;
;;

(*
let rec cutelim proof = 
  let _, _, rule = applytohyps proof in
  match rule with
  | SCcut (e, proof1, proof2) ->
    let prf = lcommute (rcommute xcutelim) proof1 proof2 e 1 in
    let g, c, r = prf in
    List.fold_left 
      (fun proof f -> sclcontr (f, prf)) prf g
  | _ -> proof

and lcommute f proof1 proof2 a n =
  let g1, _, rule1 = proof1 in
  let ga, b, rule2 = proof2 in
  let g2 = rm a ga in
  match rule1 with
  | SCaxiom (e) -> 
    sclcontr (a, addhyp (rm g1 a) proof2)
  | SClfalse -> sclfalse ((rm efalse g1)@g2)
  | SCrfalse (e) -> addhyp g2 (scrfalse (b))
  | SClnot (c, prf) -> addhyp g2 (sclnot (c, b, prf))
  | SCcnot (e, prf) ->
    sccnot (
      b, lcommute f (scrnot (a, sclnot (b, proof2))) prf (enot a))
  | SClimply (e1, e2, prf1, prf2) -> 
    sclimply (
      e1, e2, 
      addhyp g2 prf1, 
      lcommute f prf2 proof2 a)
  | SClcontr (e, prf) | SCland (e1, e2, prf)
  | SClor (e1, e2, prf1, prf2)
  | SClall (e1, e2, prf) | SClex (e1, e2, proof) 
    -> applytohyps (fun prf -> lcommute f prf proof2 a n) proof2
  | SCtrue | SCeqref (e) | SCeqsym (e1, e2)
  | SCeqprop (e1, e2, prfs) | SCeqfunc (e1, e2, prfs)
  | SCrand (e1, e2, prf1, prf2)
  | SCrorl (e1, e2, prf) | SCrorr (e1, e2, prf)
  | SCrimply (e1, e2, prf) | SCrnot (e, prf)
  | SCrall (e1, e2, prf) | SCrex (e1, t, prf)
    -> f proof1 proof2 a n

and rcommute f proof1 proof2 a n =
  let g1, _, rule1 = proof1 in
  let ga, b, rule2 = proof2 in
  let rec rma g = match n with
    | 0 -> g
    | n -> rm a (rma g) in
  let g2 = rma ga in
  match rule2 with
  | SCeqsym (x, y) when (equal a (eapp ("=", [x; y])))
  | SCeqprop (e1, e2, prfs) when (equal a e1)
  | SCland (e1, e2, prf) when (equal a (eand (e1, e2)))
  | SClor (e1, e2, prf1, prf2) when (equal a (eor (e1, e2)))
  | SClimply (e1, e2, prf1, prf2) when (equal a (eimply (e1, e2)))
  | SClnot (e, prf) when (equal a (enot e))
  | SClall (e1, e2, prf) when (equal a e1)
  | SClex (e1, e2, prf) when (equal a e1)
      -> f proof1 proof2 a n
  | SCaxiom (e) -> 
    if equal e a
    then addhyp g2 proof1
    else scaxiom (e, g1@g2)
  | SClfalse -> 
    if equal a efalse
    then scrfalse (b, addhyp g2 proof1)
    else sclfalse (g1@rm efalse g2, b)
  | SCtrue ->
    sctrue (g1@g2)
  | SCeqref (x) -> 
    sceqref (x, g1@g2)
  | SCeqsym (x, y) -> 
    sceqsym (x, y, g1@rm (eapp ("=", [x; y])) g2)
  | SClcontr (e, prf) when (equal a e) -> 
    rcommute f proof1 prf a (n+1)
  | SCeqprop (e1, e2, prfs) | SCeqfunc (x, y, prfs)
  | SCrfalse (e, prf) | SClcontr (e, prf)
  | SCland (e1, e2, prf) | SClor (e1, e2, prf1, prf2)
  | SClimply (e1, e2, prf1, prf2) | SClnot (e, prf)
  | SClall (e1, e2, prf) | SClex (e1, e2, prf)
  | SCrand (e1, e2, prf1, prf2) | SCrorl (e1, e2, prf)
  | SCrorr (e1, e2, prf) | SCrimply (e1, e2, prf)
  | SCrnot (e, prf) | SCrall (e1, e2, prf)
  | SCrex (e1, e2, prf) | SCcnot (e, prf)
    -> applytohyps (fun prf -> rcommute f proof1 prf a n) proof2

and xcutelim proof1 proof2 a n =
  if n = 0 then proof2
  else
    match proof1, proof2 with
(*  | SCtrue -> g, c, SCtrue
    | SCeqref (e) -> g, c, SCeqref (e)
    | SCeqsym (e1, e2) -> g, c, SCeqsym (e1, e2)
    | SCeqprop (e1, e2, prfs) -> 
      sceqprop (e1, e2, List.map f proofs)
    | SCeqfunc (e1, e2, prfs) -> 
      sceqfunc (e1, e2, List.map f proofs)
    | SCrand (e1, e2, prf1, prf2) ->
      scrand (e1, e2, f proof1, f proof2)
    | SCrorl (e1, e2, prf) -> 
      scrorl (e1, e2, f proof)
    | SCrorr (e1, e2, prf) ->
      scrorr (e1, e2, f proof)
    | SCrimply (e1, e2, prf) ->
      scrimply (e1, e2, f proof)
    | SCrnot (e, prf) -> scrnot (e, f proof)
    | SCrall (e1, e2, prf) -> scrall (e1, e2, f proof)
    | SCrex (_, t, prf1), SClex (_, v, prf2) ->
      lcommute (rcommute xcutelim) 
	(lcommute (rcommute xcutelim) proof1 prf2) 
	prf2 *)
    | _ -> assert false
;;
*)
(*
let cl e = match e with
  | Etrue -> enot (enot (etrue))
  | Efalse -> enot (enot (efalse))
  | Evar (s, _) -> evar (s);
  | Eapp ("=", args, _) -> enot (enot (eapp ("=", args)))
  | Eapp (s, args, _) -> eapp (s, args)
  | Eand (e1, e2, _) -> 
    enot (enot (eand (enot (enot e1),enot (enot e2))))
  | Eor (e1, e2, _) ->
    enot (enot (eor (enot (enot e1),enot (enot e2))))
  | Eimply (e1, e2, _) ->
    enot (enot (eimply (enot (enot e1),enot (enot e2))))
  | Enot (e, _) -> enot (enot (enot (enot (enot e))))
  | Eall (Evar (v, _), s, e, _) ->
    enot (enot (eall (evar (v), s, enot (enot e))))
  | Eex (Evar (v, _), s, e, _) ->
    enot (enot (eex (evar (v), s, enot (enot e))))
  | Eex _ | Eall _ | Etau _ 
  | Elam _ | Emeta _ | Eequiv _ -> 
    assert false
;;
*)
