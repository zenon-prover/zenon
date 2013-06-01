(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
Version.add "$Id$";;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Printf;;
open Super_hashtab;;



let ( =%= ) = ( = );;
let ( = ) = Expr.equal;;

type state = {
  queue : queue;
};;

type branch_state =
  | Open
  | Closed of (proof*(Expr.expr * Expr.goalness) list list)
  | Backtrack
;;

type frame = {
  node : node;
  state : state;
  brst : branch_state array;
  curbr : int;
};;

(***************)

let cur_depth = ref 0;;
let top_depth = ref 0;;
let max_depth = ref 1_000_000_000;;

let steps = ref 0.;;

(****************)




let add_node st n =
  { (*st with*) queue = insert st.queue n }
;;

let add_node_list st ns =
  List.fold_left add_node st ns
;;


let rec is_conj f m =
  if m <= 0 then 0 else
  match f with
  | Eand (a, b, _) -> is_conj b (is_conj a m)
  | Enot (a, _) -> is_disj a m
  | _ -> m-1

and is_disj f m =
  if m <= 0 then 0 else
  match f with
  | Eor (a, b, _) -> is_disj b (is_disj a m)
  | Eimply (a, b, _) -> is_disj b (is_conj a m)
  | Enot (a, _) -> is_conj a m
  | _ -> m-1
;;

let rec decomp_conj neg accu f =
  match f with
  | Eand (a, b, _) -> decomp_conj neg (decomp_conj neg accu b) a
  | Enot (a, _) -> decomp_disj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu

and decomp_disj neg accu f =
  match f with
  | Eor (a, b, _) -> decomp_disj neg (decomp_disj neg accu b) a
  | Eimply (a, b, _) -> decomp_conj (not neg) (decomp_disj neg accu b) a
  | Enot (a, _) -> decomp_conj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu
;;

let newnodes_absurd st fm g =
  match fm with
  | Enot (p, _) when member_he p -> add_node st {
      nconc = [fm; p];
      nrule = Close (p);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | p when member_he (enot p) -> add_node st {
      nconc = [p; enot p];
      nrule = Close (p);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | _ -> st, false
;;

let newnodes_closure st fm g =
  match fm with
  | Efalse -> add_node st {
      nconc = [fm];
      nrule = False;
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Enot (Etrue, _) -> add_node st {
      nconc = [fm];
      nrule = NotTrue;
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Enot (Eapp (s, [a; b], _), _) when Eqrel.refl s && Expr.equal a b ->
    add_node st {
      nconc = [fm];
      nrule = Close_refl (s, a);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Eapp (s, [e1; e2], _)
    when Eqrel.sym s && member_he (enot (eapp (s, [e2; e1]))) ->
    add_node st {
      nconc = [fm; (enot (eapp (s, [e2; e1])))];
      nrule = Close_sym (s, e1, e2);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Enot (Eapp (s, [e1; e2], _), _)
    when Eqrel.sym s && member_he (eapp (s, [e2; e1])) ->
    add_node st {
      nconc = [fm; (eapp (s, [e2; e1]))];
      nrule = Close_sym (s, e2, e1);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Eapp ("=", [Eapp ("$string", [v1], _);
                Eapp ("$string", [v2], _)], _) when not (Expr.equal v1 v2) ->
     add_node st {
       nconc = [fm];
       nrule = Ext ("", "stringequal", [v1; v2]);
       nprio = Prop;
       ngoal = g;
       nbranches = [| |];
     }, true
  | _ -> st, false
;;


let newnodes_jtree st fm g =
  match fm with
  | Eand _ | Enot (Eor _, _) | Enot (Eimply _, _)
    when is_conj fm 3 == 0 ->
      add_node st {
        nconc = [fm];
        nrule = ConjTree fm;
        nprio = Prop;
        ngoal = g;
        nbranches = [| decomp_conj false [] fm |];
      }, true
  | Eor _ | Enot (Eand _, _) | Eimply _
    when is_disj fm 3 == 0 ->
      let forms = Array.of_list (decomp_disj false [] fm) in
      let branches = Array.map (fun x -> [x]) forms in
      add_node st {
        nconc = [fm];
        nrule = DisjTree fm;
        nprio = Prop;
        ngoal = g;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_alpha st fm g =
  match fm with
  | Enot (Enot (a, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotNot (a);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a] |];
      }, true
  | Eand (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = And (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a; b] |];
      }, true
  | Enot (Eor (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotOr (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a); enot (b)] |];
      }, true
  | Enot (Eimply (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotImpl (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a; enot (b)] |];
      }, true
  | _ -> st, false
;;

let newnodes_beta st fm g =
  match fm with
  | Eor (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = Or (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a]; [b] |];
      }, true
  | Eimply (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = Impl (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a)]; [b] |];
      }, true
  | Enot (Eand (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotAnd (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a)]; [enot (b)] |];
      }, true
  | Eequiv (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = Equiv (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a); enot (b)]; [a; b] |];
      }, true
  | Enot (Eequiv (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotEquiv (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a); b]; [a; enot (b)] |];
      }, true
  | _ -> st, false
;;


let newnodes_delta st fm g =
  match fm with
  | Eex (v, t, p, _) ->
     let h = substitute [(v, etau (v, t, p))] p in
     add_node st {
       nconc = [fm];
       nrule = Ex (fm);
       nprio = Prop;
       ngoal = g;
       nbranches = [| [h] |];
     }, true
  | Enot (Eall (v, t, p, _), _) ->
     let h1 = substitute [(v, etau (v, t, enot p))] (enot p) in
     let h2 = eex (v, t, enot p) in
     add_node st {
       nconc = [fm];
       nrule = NotAllEx (fm);
       nprio = Prop;
       ngoal = g;
       nbranches = [| [h1; h2] |];
     }, true
  | _ -> st, false
;;

let newnodes_gamma st fm g =
  match fm with
  | Eall (v, t, p, _) ->
      let w = emeta (fm) in
      let branches = [| [Expr.substitute [(v, w)] p] |] in
      add_node st {
        nconc = [fm];
        nrule = All (fm, w);
        nprio = Arity;
        ngoal = g;
        nbranches = branches;
      }, true
  | Enot (Eex (v, t, p, _) as fm1, _) ->
      let w = emeta (fm1) in
      let branches = [| [enot (Expr.substitute [(v, w)] p)] |] in
      add_node st {
        nconc = [fm];
        nrule = NotEx (fm, w);
        nprio = Arity;
        ngoal = g;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_useless st fm g =
  match fm with
  | Evar _ | Enot (Evar _, _)
  | Etau _ | Enot (Etau _, _)
    -> st, true
  | Etrue | Enot (Efalse, _)
    -> st, true
  | _ -> (st, false)
;;

(* TODO permettre aux extensions de modifier l'etat ? *)

let add_nodes st fm g =
  let combine (state, stop) f =
    if stop then (state, true) else f state fm g
  in
  let (st1, stop1) =
    List.fold_left combine (st, false) [
      newnodes_absurd;
      newnodes_closure;
    ]
  in
  (* Désactive l'utilisation des super-règles pour calculer les nouvelles
     super_règles *)
  (* let (newnodes2,stop2)= [],false in *)
  (* Active l'utilisation des super-règles pour calculer les nouvelles
     super_règles *)
  let (newnodes2,stop2)=Node.relevant (Extension.newnodes fm g []) in
  let insert_node s n = { queue = insert s.queue n} in 
  let st2 = List.fold_left insert_node st1 newnodes2 in
  let (st3, stop3) =
    List.fold_left combine (st2, stop2) [
      newnodes_jtree;
      newnodes_alpha;
      newnodes_beta;
      newnodes_delta;
      newnodes_gamma;
      newnodes_useless;
    ]
  in
 if not stop3 then add_he fm g;
 st3
;;

let rec reduce_list accu l =
  match l with
  | Enot (Efalse, _) :: t
  | Etrue :: t
  | Enot (Eapp ("TLA.in", [_; Evar ("TLA.emptyset", _)], _), _) :: t
    -> reduce_list accu t
  | Eapp (s, [e1; e2], _) :: t when Expr.equal e1 e2 && Eqrel.refl s ->
      reduce_list accu t
  | Eapp (s, [e1; e2], _) as f :: t when Eqrel.sym s ->
      let g = eapp (s, [e2; e1]) in
      if member_he f || member_he g
         || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
      then reduce_list accu t
      else reduce_list (f :: accu) t
  | Enot (Eapp (s, [e1; e2], _), _) as f :: t when Eqrel.sym s ->
     let g = enot (eapp (s, [e2; e1])) in
     if member_he f || member_he g
        || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | f :: t ->
     if member_he f || List.exists (Expr.equal f) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | [] -> accu
;;

let reduce_branches n =
  let reduced = Array.map (reduce_list []) n.nbranches in
  let rec array_exists f a i =
    if i >= Array.length a then false
    else if f a.(i) then true
    else array_exists f a (i+1)
  in
  if array_exists (function [] -> true | _ -> false) reduced 0
  then None
  else Some { n with nbranches = reduced }
;;

let sort_uniq l =
  let l1 = List.sort Expr.compare l in
  let rec uniq l accu =
    match l with
    | [] | [_] -> l @ accu
    | x :: (y :: _ as t) when Expr.equal x y -> uniq t accu
    | x :: t -> uniq t (x :: accu)
  in
  uniq l1 []
;;

let rec not_meta_eq e =
  match e with
  | Eapp ("=", ([Emeta _; _] | [_; Emeta _]), _) -> false
  | Eapp (_, ([Evar ("_", _); Emeta _; _] | [_; Emeta _]), _) ->
     false (* FIXME HACK see ext_focal.ml *)
  | Eand (e1, e2, _)
  | Eor (e1, e2, _)
  -> not_meta_eq e1 || not_meta_eq e2
  | _ -> true
;;

let get_meta_weight e = if get_metas e =%= [] then 1 else 0;;

let count_meta_list l =
  let l = List.filter not_meta_eq l in
  let l = sort_uniq (List.flatten (List.map get_metas l)) in
  List.fold_left (fun x y -> x + get_meta_weight y) 0 l
;;

let rec not_trivial e =
  match e with
  | Enot (Eapp ("=", ([Emeta _; _] | [_; Emeta _]), _), _) -> false
  | Enot (Eapp ("TLA.in", [Emeta _; Evar ("TLA.emptyset", _)], _), _) -> true
  | Enot (Eapp ("TLA.in", [Emeta _; Evar _], _), _) -> false
  | Eand (e1, e2, _) | Eor (e1, e2, _) -> not_trivial e1 || not_trivial e2
  | _ -> true
;;

let count_nontrivial l = List.length (List.filter not_trivial l);;

let rndstate = ref (Random.State.make [| 0 |]);;

let find_open_branch node brstate =
  let last = Array.length brstate - 1 in
  if brstate =%= [| |] then None
  else if brstate.(last) =%= Open
          && List.exists not_meta_eq node.nbranches.(last)
    then Some last
  else begin
    let rec loop accu i =
      if i < 0 then accu
      else if brstate.(i) =%= Open then loop (i::accu) (i-1)
      else loop accu (i-1)
    in
    let open_branches = loop [] last in
    match open_branches with
    | [] -> None
    | [i] -> Some i
    | l ->
        let score i =
          let fs = node.nbranches.(i) in
          let f accu x = accu + Expr.size x in
          let s = List.fold_left f 0 fs in
          (fs, count_nontrivial fs, count_meta_list fs, s, i)
        in
        let l1 = List.rev_map score l in
        let cmp (fs1, nt1, len1, size1, _) (fs2, nt2, len2, size2, _) =
          if nt1 =%= 0 then 1
          else if nt2 =%= 0 then -1
          else if len1 <> len2 then len2 - len1
          else size1 - size2
        in
        let l2 = List.sort cmp l1 in
        if !Globals.random_flag then begin
          let l = List.length l2 in
          let n = Random.State.int !rndstate l in
          match List.nth l2 n with (_, _, _, _, i) -> Some i
        end else begin
          match l2 with
          | (_, _, _, _, i) :: _ -> Some i
          | _ -> assert false
        end
  end
;;

let dummy_proof = {
  mlconc = [];
  mlrule = False;
  mlhyps = [| |];
  mlrefc = 0;
};;


let good_lemma rule =
  match rule with
  | Close _ | Close_refl _ | Close_sym _ | False | NotTrue -> false
  | _ -> true
;;

(* there is no [Open] in [branches]; make a proof node *)
let make_result n nbranches branches =
  let concs = ref []
  and proofs = ref []
  in
  for i = 0 to Array.length nbranches - 1 do
    match nbranches.(i) with
    | Open | Backtrack -> assert false
    | Closed (p,_) ->
        proofs := p :: !proofs;
        concs := union (diff p.mlconc n.nbranches.(i)) !concs;
  done;
  assert (List.length !proofs == Array.length n.nbranches);
  let prf_node = {
    mlconc = union n.nconc !concs;
    mlrule = n.nrule;
    mlhyps = Array.of_list (List.rev !proofs);
    mlrefc = 1;
  } in
  
  Closed (prf_node,branches) 		(* a ne pas supprimer sinon *)
;;        				(* problème pour les règles de closures *)

let good_head q =
  match head q with
  | None -> true
  | Some node -> good_lemma node.nrule
;;

exception SuperLimitsExceeded;;


let periodic c =
  Super_globals.progress_counter := !Super_globals.progress_period;
  Progress.do_progress (fun () -> ()) c;
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let tm = Sys.time () in
  if tm > !Super_globals.progress_last +. 0.001 then begin
    let new_period = 
      float !Super_globals.progress_period *. Super_globals.period_base
      /. (tm -. !Super_globals.progress_last) in
    Super_globals.progress_period := int_of_float new_period;
  end;
  if !Super_globals.progress_period < 1 then Super_globals.progress_period := 1;
  Super_globals.progress_last := tm;
  if tm > (Super_globals.time_limit_super ()) then begin
    raise SuperLimitsExceeded;
  end;
  if float heap_size > !Globals.size_limit then begin
    Progress.end_progress "";
    raise SuperLimitsExceeded;
  end;
  if !steps > !Globals.step_limit then begin
    Progress.end_progress "";
    raise SuperLimitsExceeded;
  end;
;;

let progress () =
  decr Super_globals.progress_counter;
  (* if !Super_globals.progress_counter < 0 then *) periodic '%';
;;

let rec refute_aux stk st forms branches =
  match forms with
  | [] ->
      next_node stk st branches
  | (Etrue, _) :: fms
  | (Enot (Efalse, _), _) :: fms
    -> refute_aux stk st fms branches
  | (Eapp (s, [e1; e2], _), _) :: fms when Eqrel.refl s && Expr.equal e1 e2 ->
      refute_aux stk st fms branches
  | (fm, g) :: fms ->
    flush stdout;
    refute_aux stk (add_nodes st fm g) fms branches

and refute stk st forms branches =
  Step.forms "refute" forms;
  refute_aux stk st forms branches

and next_node stk st branches =
  progress ();
  incr Globals.inferences;
  match remove st.queue with
  | None ->  
      unwind stk 
	(Closed 
	   (dummy_proof,
	    ( (get_all_he()))::branches))
	((  (get_all_he())) ::branches)
      
  | Some (n, q1) ->
      let st1 = { queue = q1} in
      match reduce_branches n with
      | Some n1 ->

         let brstate = Array.make (Array.length n.nbranches) Open in
         next_branch stk n1 st1 brstate branches
      | None -> next_node stk st1 branches

and next_branch stk n st brstate branches =
  Step.rule "next_branch" n.nrule;
  match find_open_branch n brstate with
  | Some i ->
      let fr = {node = n; state = st; brst = brstate; curbr = i} in
      incr cur_depth;
      if !cur_depth > !top_depth then top_depth := !cur_depth;
      if !cur_depth > !max_depth then begin
        unwind stk Backtrack branches
      end else begin
        refute (fr :: stk) st (List.map (fun x -> (x, n.ngoal)) n.nbranches.(i))
       branches end
  | None ->
      let result = make_result n brstate branches in
      unwind stk result branches

and unwind stk res branches =
  decr cur_depth;
  match stk with
  | [] -> res
  | fr :: stk1 ->
      Step.rule "unwind" fr.node.nrule;
      let f x =
        if member_he x then begin (* we can unwind before adding all forms *)
          Extension.remove_formula x;
          remove_he x;
	end;
      in
      List.iter f (List.rev fr.node.nbranches.(fr.curbr));
      begin match res with
      | Backtrack -> unwind stk1 res branches
      | Closed _ ->
          fr.brst.(fr.curbr) <- res;
          next_branch stk1 fr.node fr.state fr.brst branches
      | Open -> assert false
      end;
;;

let rec reduce_initial_list accu l =
  match l with
  | [] -> accu
  | (n, f,i) as fp :: t ->
      if List.exists (fun (n, e,_) -> Expr.equal f e) accu
      then reduce_initial_list accu t
      else reduce_initial_list (fp :: accu) t
;;

let ticker finished () =
  let tm = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  Progress.do_progress begin fun () ->
    eprintf "depth %5d/%d  search %d  proof %d  \
             lemma %d  size %dM  time %.0f\n"
            !cur_depth !top_depth !Globals.inferences !Globals.proof_nodes
            !Globals.stored_lemmas (heap_size / 1_000_000) tm;
    Expr.print_stats stderr;
  end '#';
  if not finished then periodic '!';
;;

let rec iter_refute rl branches =
  match refute [] {queue = empty} rl branches with
  | Backtrack ->
      max_depth := 2 * !max_depth;
      Progress.do_progress begin fun () ->
        eprintf "increase max_depth to %d\n" !max_depth;
      end '*';
      iter_refute rl branches;
  | x -> x
;;

exception NoOrientedRule;;

let rec is_atomic expr =
  match expr with
  | Eand _  | Eor _  | Eimply _ | Eequiv _
  | Eall _ | Eex _ | Elam _-> false
  | Enot (e,_) -> is_atomic e
  | _ -> true;;

let has_cst_prof2 e =
  let rec list_bool_n l b0 i : (bool*int)=
    match l with
      |[] -> (b0,i)
      |(b,n)::q -> if (b&&n>i) then list_bool_n q true n
	else list_bool_n q b0 i
  in 
  let rec aux n expr : (bool*int)=
    match expr with
      |Eapp (_,[],_) -> (true,n)
      |Eapp (_,a,_) -> 
	list_bool_n (List.map (aux (n+1)) a) false 0
      |Eall (_,_,a,_)
      |Eex (_,_,a,_) ->  aux (n+1) a
      |Enot (e,_) -> aux (n+1) e
      |Eand (a,b,_)
      |Eor (a,b,_)
      |Eimply (a,b,_)
      |Eequiv (a,b,_)-> 
	let (ba,na) = (aux (n+1) a) 
	and (bb,nb) = (aux (n+1) b)
	in 
	if ba&&bb 
	then (true,max na nb)
	else 
	  if ba then (ba,na)
	  else (bb,nb)
      |_ -> (false,n)
  in 
  let (bool,n)=aux 0 e in
  bool && (n>=2)
;;
   

let rec is_app expr =
  match expr with
    |Eapp (_,[],_) -> false
    |Eapp _ -> true
    |Enot (e,_) -> is_app e
    |_ -> false;;

let rec is_2app expr =
  match expr with
    |Eapp (_,a,_) -> 
      List.exists is_app a
    |Enot (e,_) -> is_2app e
    |_ -> false
;;

let negation e =
  match e with
    |Enot(e1,_) -> e1
    |_ -> enot e
;;

let rec diff2 l1 l2 =
  match l1 with
  | [] -> []
  | e::t -> if List.exists ((==) e) l2
            then diff2 t l2
            else e :: (diff2 t l2)
;;

(* dernier test :
une règle F(X,Y) -> G(X,Y,Z) n'est pas correcte car
Z n'est pas une méta, on ne sait rien sur elle.
*)
let test_orient e1 e2 newnodes =
  if !Globals.debug_flag then
    begin
      Print.expr (Print.Chan stdout) e1;
      Printf.printf "-->";
      Print.expr (Print.Chan stdout) e2;
      Printf.printf "\n";
      if not(has_cst_prof2 e1)  then Printf.printf "ok cst\n";
      if is_atomic e1 then Printf.printf "atomic\n";
      if not (Super_match_rules.is_egal e1 newnodes) then Printf.printf "not egal\n";
      if not (Super_match_rules.is_plusGrand e1 e2) then Printf.printf "not plusGrand\n";
      if not (Super_match_rules.is_extensionnality e1) 
      then Printf.printf "not extensionnal\n";
      if not (is_2app e1) then Printf.printf "not 2app\n";
      if (diff2 (Expr.get_fv e2) (Expr.get_fv e1)) == [] 
      then Printf.printf "fv e2 inclus dans fve1\n"
    end;
  is_atomic e1 
  && not (Super_match_rules.is_egal e1 newnodes) 
  && not (Super_match_rules.is_plusGrand e1 e2) 
  && not (Super_match_rules.is_extensionnality e1)
  && not(has_cst_prof2 e1) 
  && (diff2 (Expr.get_fv e2) (Expr.get_fv e1)) == []
;; 



let rec get_const e =
  match e with
    |Eapp(s,[],_) ->  [e]
    |Eapp(s,l_e,_) -> 
      List.fold_left 
	(fun a e -> union (get_const e) a) [] l_e
    |Enot(e,_) 
    |Eall(_,_,e,_)
    |Eex(_,_,e,_) 
    |Etau(_,_,e,_)
    |Elam(_,_,e,_)-> get_const e
    |Eand(e1,e2,_) 
    |Eor(e1,e2,_) 
    |Eimply(e1,e2,_) 
    |Eequiv(e1,e2,_) -> 
      Expr.union 
	(get_const e1)
	(get_const e2)
    |_ -> []
;;

let rec substitute_cst map e =
  match e with
  | Evar (v, _) -> e
  | Emeta _ -> e
  | Eapp (s,[],_) ->
    (try List.assq e map
     with Not_found -> e)
  | Eapp (s, args, _) ->
     let acts = List.map (substitute_cst map) args in
     eapp (s, acts)
  | Enot (f, _) -> enot (substitute_cst map f)
  | Eand (f, g, _) -> eand (substitute_cst map f, substitute_cst map g)
  | Eor (f, g, _) -> eor (substitute_cst map f, substitute_cst map g)
  | Eimply (f, g, _) -> eimply (substitute_cst map f, substitute_cst map g)
  | Eequiv (f, g, _) -> eequiv (substitute_cst map f, substitute_cst map g)
  | Etrue | Efalse -> e
  | Eall (v, t, f, _) ->  eall (v, t, substitute_cst map f)
  | Eex (v, t, f, _) ->  eex (v, t, substitute_cst map f)
  | Etau (v, t, f, _) -> etau (v, t, substitute_cst map f)
  | Elam (v, t, f, _) -> elam (v, t, substitute_cst map f)
;;


let constr_rule_const const n e1 e2 i =
  let rec gener_newvar l =
    match l with
      |[] -> []
      |a::q -> 
	(a,newvar ())::(gener_newvar q)
  in 
  let map = gener_newvar const in
  let new_e1 = substitute_cst map e1 
  and new_e2 = substitute_cst map e2 in
  (n,
   new_e1,
   List.fold_left 
     (fun 
       a 
       (x,y) ->  
	 eor(a,enot(eapp("=",[x;y])))) 
     new_e2
     map,
   i)
;;

let rec extrait_e1 l =
  match l with
    |[] -> []
    |(_,e1,_,_)::q -> e1::(extrait_e1 q)
;;


let rec orient_rule expr newnodes =
  let new_rule n e1 e2 i =
    if test_orient e1 e2 newnodes
    then ([(n,e1,e2,i)])
    else ([] )
  in
  match expr with
    | (n,Eall(_,_,e,_),i) ->
      orient_rule (n,e,i) newnodes
    | (n,Eequiv (e1,e2,_),i) -> 
      let not_e1 = negation e1
      and not_e2 = negation e2 
      and not_n = "not_"^n in
      let res =
	(new_rule n e1 e2 i)
	@(new_rule not_n not_e1 not_e2 i)
      in 
      if res == [] then raise NoOrientedRule else res,extrait_e1 res
    | (n,Eimply (e1,e2,_),i) ->
      let not_e1 = negation e1
      and not_e2 = negation e2 
      and n_ctrp = n^"ctrp" in
      let res =
	(new_rule n e1 e2 i)
	@(new_rule n_ctrp not_e2 not_e1 i)
      in
       if res == [] then raise NoOrientedRule else res,extrait_e1 res
    | (n,Eapp("=",_,_),_) -> raise NoOrientedRule
    | (n,e,i) ->
      if test_orient e efalse newnodes
      then
      	let not_e = negation e in
    	let res = (new_rule n not_e efalse i)
    	in
	if res == [] then raise NoOrientedRule else res,extrait_e1 res
      else raise  NoOrientedRule
;;

let rec is_axiom_atomic e =
  match e with
    |(n,Eall(_,_,e,_),i) -> is_axiom_atomic (n,e,i)
    |(_,Eequiv (_,_,_),_) | (_,Eimply (_,_,_),_) -> false
    |_ -> true
;;

let orient_rule_list l_expr =
  let rec aux l l_expr l_def l_mg=
    match l with
      |[] -> (List.rev l_expr,List.rev l_def)
      |e ::q ->
	periodic '!';
	try 
	  let (nv,mg) = orient_rule e l_mg in
	    aux q (l_expr@nv) l_def (l_mg@mg)
	with
	  |NoOrientedRule ->
	    aux q l_expr (l_def@[e]) l_mg
  in aux l_expr [] [] [];;

let separate l_init =
  let rec aux hyp conj l =
    match l with
      |[] -> hyp,conj
      |Phrase.Hyp(n,e,0)::q -> aux hyp ((n,e,0)::conj) q
      |Phrase.Hyp(n,e,i)::q -> aux ((n,e,i)::hyp) conj q
      |a::q -> aux hyp conj q
  in aux [] [] l_init;;

let rec suppr_name l =
  match l with
    |[] -> []
    |(_,e,i)::q -> (e,i)::(suppr_name q);;


let print_rules tb =
  Printf.printf "\nnombre de regles:%d\n" (Hashtbl.length tb);
  let rec util f sep l =
    match l with
      |[] -> ()
      |[a] -> f a
      |a::qa -> f a;print_string sep;util f sep qa
  in
  let print_branches lb =
    util (fun a ->
      util (fun b -> Print.expr_soft (Print.Chan stdout) b) ";" a) "|" lb
  in
  Hashtbl.iter
    (fun c -> fun r ->
      Printf.printf "%s :" (fst r);
      Print.expr_soft (Print.Chan stdout) c;
      print_string "-->";
      print_branches (snd r);
      print_string "\n";) tb
;;
   	

let form_node expr1 g b = 
  let mknode prio name args =
    [ Node {
      nconc = [expr1];
      nrule = Ext ("B", name, expr1::(List.concat b)@args);
      nprio = prio;
      ngoal = g;
      nbranches = Array.of_list b;
    } ]
  in
  match expr1 with
    | Eapp (e1, [_;Eapp(op,en,_)],_) ->
      mknode Prop op (en)
    | _ -> assert false
;;
      
let make_expr e args =
  match e with
    | Eapp (s,[_;Eapp(op,_,_)],_) ->
      eapp(s,[List.hd args;eapp(op,List.tl args)])
    | _ -> assert false
;;
      
let snd_list_list l =
  List.map (fun li -> List.map fst li) l;;

let to_sded l =
  if !Globals.random_flag then begin
    rndstate := Random.State.make [| !Globals.random_seed |];
    max_depth := 100;
  end;
  (* let al = Gc.create_alarm (ticker false) in *)
  let rl = reduce_initial_list [] l in
  let (nl,l_def) = orient_rule_list rl in
  
  Globals.inferences := 0;
  Globals.proof_nodes := 0;
  cur_depth := 0;
  top_depth := 0;
  try
    Super_match_rules.init_ext "SZ";
    let rec aux l =
      match l with
	|[] -> 
	  if !Globals.debug_flag then
	    print_rules rules;
	  ()
	|(n,e1,e2,i)::q -> 
	  flush_all();
	  HE.clear allforms;
	  let iter_pos = iter_refute [(e2,i)] [] in
	  match (iter_pos) with
	      | Closed(p,res) ->
		Hashtbl.add rules e1 (n,snd_list_list res) ;
		Super_match_rules.maj_all "SZ" n e1 (snd_list_list res);
		(* Pour génerer le fichier d'extension ocaml sz.ml *)
		(* Print_ext.print_all "sz.ml"; *)
		(* Toploop.initialize_toplevel_env (); *)
		(* let _ = Toploop.use_file Format.std_formatter "sz.ml" in *)
		aux q
	      | _  -> assert false
    in
    aux nl;
    (* Gc.delete_alarm al; *)
    ticker true ();
    Mlproof.make_f,l_def
    
  with e ->
    Progress.end_progress " no proof";
    raise e
;;

