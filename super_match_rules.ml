(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
Version.add "$Id$";;

open Super_hashtab;;
open Extension;;
open Expr;;
open Node;;
open Mlproof;;

let rec print_newnodes_mg l =
  match l with
    |[] -> Printf.printf "\n"
    |e::q -> 
      Print.expr (Print.Chan stdout) e;
      Printf.printf ";"; print_newnodes_mg q
;;

let rec util f sep l =
  match l with
    |[] -> ()
    |[a] -> f a
    |a::qa -> f a;print_string sep;util f sep qa
;;

let print_branches lb =
  util (fun a ->
    util (fun b -> Print.expr (Print.Chan stdout) b) ";" a) "|" lb
    ;;

let print_rule n a b =
  Printf.printf "%s :" n;
  Print.expr (Print.Chan stdout) a;
  print_string "-->";
  print_branches b;
  print_string "\n"
;;


(* table de hachage qui conserve les règles sous forme nom,branches *)
(* utile pour ll_to_args *)
let tb_branches : ((string,expr list list) Hashtbl.t)= Hashtbl.create 999997 ;;

let init_ext name =
  Extension.register {
    Extension.name = name;
    Extension.newnodes = (fun x y _ -> []);
    Extension.make_inst = (fun x y z -> assert false);
    Extension.add_formula = (fun x -> ());
    Extension.remove_formula = (fun x -> ());
    Extension.preprocess = (fun x -> x);
    Extension.add_phrase = (fun x -> ());
    Extension.postprocess = (fun x -> x);
    Extension.to_llproof = (fun x y z -> assert false);
    Extension.p_rule_coq = (fun x y -> assert false);
    Extension.declare_context_coq = (fun x -> ());
    Extension.predef = (fun () ->[]);
  };
  Extension.activate name
;;

(**************** unification ************* *****)

exception Non_unifiable;;
exception Non_insere;;

let rec suppr_doublons l =
  match l with
    |[] -> []
    |e::q -> if List.mem e q then suppr_doublons q else e::(suppr_doublons q)

let unifie a b = 
  let rec aux aa bb =
    match aa,bb with
      |Evar _, _ | _, Evar _
      |Etau _, _ | _,Etau _ -> [(aa,bb)]
      |Emeta _, _  | _,Emeta _ -> [(aa,bb)]
      |Eapp (s1,el1,_),Eapp (s2,el2,_)
      	when s1 = s2 ->
	begin
	  try
      	    List.concat (List.map2 (fun x -> fun y -> aux x y) el1 el2)
	  with Invalid_argument _ -> 
	    Prove.arity_warning s1; 
	    raise Non_unifiable
	end
      |Enot(e1,_),Enot(e2,_) ->	aux e1 e2
      |Eand(e1,e2,_),Eand(e3,e4,_) 
      |Eor(e1,e2,_),Eor(e3,e4,_) 
      |Eimply(e1,e2,_),Eimply(e3,e4,_) 
      |Eequiv(e1,e2,_),Eequiv(e3,e4,_)
      |Eall(e1,_,e2,_),Eall(e3,_,e4,_)
      |Eex(e1,_,e2,_),Eex(e3,_,e4,_)
      |Elam(e1,_,e2,_),Elam(e3,_,e4,_)	->
	(aux e1 e3)@(aux e2 e4)
      |_ -> 
	raise Non_unifiable
  in suppr_doublons (aux a b)
;;

type ordre =
  | Plus_petit
  | Plus_grand
  | Egal
  | None;;

let is_atom a =
  match a with
    |Evar _ -> true 
    |Etau _ |Emeta _-> assert false
    |_ -> false
;;

let ordre a b =
  if is_atom a
  then 
    if is_atom b then Egal
    else Plus_grand
  else 
    if is_atom b then Plus_petit
    else assert false
;;


let print_res l_c =
  Printf.printf "res=";
  List.iter (fun x -> 
    Printf.printf "(";
    Print.expr (Print.Chan stdout) (fst x);
    Printf.printf ",";
    Print.expr (Print.Chan stdout) (snd x);
     Printf.printf ")")
    l_c;
  Printf.printf "\n"
;;

let unificateur_to_string u =
  match u with
    | Plus_petit -> "<"
    | Plus_grand -> ">"
    | Egal -> "="
    | None -> "<>"
;;

let plus_petit a b =
  try 
    let unificateur = unifie a b in
    if unificateur = [] then None else
    let tete = List.hd unificateur in 
    let ordre_init = ordre (fst tete) (snd tete) in
    let rec aux unif o =
      match unif with
	|[] -> o
	|(a,b)::q -> 
	  let new_ordre = ordre a b in
	  if o = Egal then aux q new_ordre
	  else if new_ordre = Egal || o=new_ordre then aux q o
	  else Egal
    in aux unificateur ordre_init
  with Non_unifiable -> None
;;


(* TEST *)
(* let a = eapp ("in", [evar("x");eapp ("cup",[evar("a");evar("b")])]);; *)
(* let b = eapp ("in", [ *)
(*   evar("X"); *)
(*   eapp ("cup", *)
(* 	[eapp ("cup",[evar("a");evar("b")]); *)
(* 	 eapp ("cup",[evar("b");evar("a")])])]);; *)
(* let res = unifie a b in *)
(* print_res res;; *)

(* let c = eapp ("+",[evar("x");evar("0")]);; *)
(* let d = eapp ("+",[evar("0");evar("x")]);; *)
(* let res = unifie c d in *)
(* print_res res;; *)
     

(* Printf.printf "a %s b\n" (unificateur_to_string (plus_petit a b));; *)
(* Printf.printf "c %s d\n" (unificateur_to_string (plus_petit c d));; *)

(**************** new_nodes  *****************)

(* fait les substitutions des metas aussi  *)
let rec substitute_3rd map e =
  match e with
  | Evar (v, _) -> (try List.assq e map with Not_found -> e)
  | Emeta (f,_) -> (try List.assq e map with Not_found -> e)
  | Eapp (s, args, _) ->
     let acts = List.map (substitute_3rd map) args in
     begin try
      let lam = List.assq (evar s) map in
      match lam, acts with
      | Elam (v, _, body, _), [a] -> substitute_3rd [(v,a)] body
      | Evar (v, _), _ -> eapp (v, acts)
      | Eapp (s1, args1, _), _ -> eapp (s1, args1 @ acts)
      | _ -> raise Higher_order
     with Not_found -> eapp (s, acts)
     end
  | Enot (f, _) -> enot (substitute_3rd map f)
  | Eand (f, g, _) -> eand (substitute_3rd map f, substitute_3rd map g)
  | Eor (f, g, _) -> eor (substitute_3rd map f, substitute_3rd map g)
  | Eimply (f, g, _) -> eimply (substitute_3rd map f, substitute_3rd map g)
  | Eequiv (f, g, _) -> eequiv (substitute_3rd map f, substitute_3rd map g)
  | Etrue | Efalse -> e
  | Eall (v, t, f, _) ->
      let map1 = Expr.rm_binding v map in
      if conflict v map1 then
        let nv = newvar () in
        eall (nv, t, substitute_3rd ((v, nv) :: map1) f)
      else
        eall (v, t, substitute_3rd map1 f)
  | Eex (v, t, f, _) ->
      let map1 = Expr.rm_binding v map in
      if conflict v map1 then
        let nv = newvar () in
        eex (nv, t, substitute_3rd ((v, nv) :: map1) f)
      else
        eex (v, t, substitute_3rd map1 f)
  | Etau (v, t, f, _) ->
      let map1 = Expr.rm_binding v map in
      if conflict v map1 then
        let nv = newvar () in
        etau (nv, t, substitute_3rd ((v, nv) :: map1) f)
      else
        etau (v, t, substitute_3rd map1 f)
  | Elam (v, t, f, _) ->
      let map1 = Expr.rm_binding v map in
      if conflict v map1 then
        let nv = newvar () in
        elam (nv, t, substitute_3rd ((v, nv) :: map1) f)
      else
        elam (v, t, substitute_3rd map1 f)
;;

let add_sans_doublons e l =
  if List.mem e l then l else l@[e];;


let rec is_unif_correct l =
  match l with
    |[] -> true
    |(a,b)::q ->
      try
	if b = List.assoc a q then 
	  is_unif_correct (List.remove_assoc a l)
	else false
      with Not_found -> is_unif_correct q;;

(* a : membre gauche de la règle *)
(* t : terme à matcher  *)
let match_t a t ext =
  let rec aux aa tt =
    match aa,tt with
      |Evar _,_ |Etau _,_ 
      |Emeta _,_  ->[(aa,tt)]
      |Eapp (s1,el1,_),Eapp (s2,el2,_)
      	when s1 = s2 ->
	begin
	  try
      	    List.concat (List.map2 (fun x -> fun y -> aux x y) el1 el2)
	  with Invalid_argument _ -> 
	    Prove.arity_warning s1; 
	    raise Non_unifiable
	end
      |Enot(e1,_),Enot(e2,_) ->	aux e1 e2
      |Eand(e1,e2,_),Eand(e3,e4,_) 
      |Eor(e1,e2,_),Eor(e3,e4,_) 
      |Eimply(e1,e2,_),Eimply(e3,e4,_) 
      |Eequiv(e1,e2,_),Eequiv(e3,e4,_)
      |Eall(e1,_,e2,_),Eall(e3,_,e4,_)
      |Eex(e1,_,e2,_),Eex(e3,_,e4,_)
      |Elam(e1,_,e2,_),Elam(e3,_,e4,_)	->
	(aux e1 e3)@(aux e2 e4)
      |_ -> 
	raise Non_unifiable
  in 
  let res = suppr_doublons (aux a t) in
  if is_unif_correct res then res else raise Non_unifiable
;;

(* TEST *)
(* let a = eapp ("in", [evar("x");eapp ("cup",[evar("a");evar("b")])]);; *)
(* let b = eapp ("in", [ *)
(*   evar("X"); *)
(*   eapp ("cut", *)
(* 	[eapp ("cup",[evar("a");evar("b")]); *)
(* 	 eapp ("cup",[evar("b");evar("a")])])]);; *)
(* let res = match_t a b in *)
(* print_res res;; *)
				     
let mknode_item e prio ext name args branches g =
    [ Node {
      nconc = [e];
      nrule = Mlproof.Ext (ext, name, args);
      nprio = prio;
      ngoal = g;
      nbranches = branches;
    } ;Stop]

let concat_sans_doublons l1 l2 =
  let rec aux l1 =
    match l1 with
      |[] -> l2
      |e::q -> if List.mem e l2 then aux q else e::(aux q)
  in aux l1;;

let get_metas_branches b =
  let rec aux1 b lm1=
    match b with
      |[] -> lm1
      |l_e::q ->
	let rec aux2 l lm2 =
	  match l with
	    |[] -> aux1 q lm2
	    |e::q2 ->
	      aux2 q2 (concat_sans_doublons (get_metas e) lm2)
	in aux2 l_e lm1
  in aux1 b [];;


let substitute_branches map branches =
  List.map (fun b ->
    List.map (fun x -> substitute_3rd map x) b) branches;;

let is_egal a l =
  let rec aux l =
    match l with
      |[] -> false
      |e::q ->
	(match plus_petit a e with
	  |Plus_petit |Plus_grand |None -> aux q
	  |Egal -> true)
  in aux l
;;

let is_plusGrand e1 e2 =
  match plus_petit e1 e2 with
    |Plus_grand -> true
    |_ -> false
;;

let is_extensionnality e1 =
  match e1 with
    |Eapp("=",[_;_],_) -> true
    |_ -> false
;;

let is_antisym e1 e2 =
  match e1,e2 with
    |Eapp(s1,_,_),Enot(Eapp(s2,_,_),_) when s1=s2 -> true
    |_ -> false
;;
      

let trouve_rang a l =
  let rec aux l n =
    match l with
      |[] -> [a],n
      |e::q -> 
	( match plus_petit a e with
	  |Plus_petit -> a::e::q,n
	  |Plus_grand |None -> 
	    let (new_q,new_n) =aux q (n+1) in
	    (e::new_q,new_n)
	  |Egal -> 
	    raise Non_insere)
  in aux l 0
;;
	     

let insere_rang_n l_a rang liste =
  match l_a with
    |[] -> liste
    |[a] -> 				(* a tester si code mort ? *)
      let rec aux l n =
	match l with
	  |[] -> [a] 			
	  |e::q -> 
	    if n=rang 
	    then a::e::q
	    else e::(aux q (n+1))
      in aux liste 0
    |[a;Stop] ->
      let rec aux l n =
	match l with
	  |[] -> [a;Stop]
	  |e::q -> 
	    if n=rang 
	    then a::Stop::e::q
	    else e::(aux q (n+1))
      in aux liste 0
    |_ -> assert false
;;



let rec do_new_var i =
  match i with
    |0 -> []
    |ni -> newvar()::(do_new_var (ni-1))
;;

(* l_var : liste des var [x;y;z] *)
(* l_meta : liste des metas [mx;my;mz]  *)
(* pour i = 2 renvoie la liste [mx;my;z] *)
let l_var_cour i l_var l_meta =
  let rec aux l n =
    match l with
      |[] -> []
      |e::q -> 
	if n<i 
	then (List.nth l_meta n)::(aux q (n+1))
	else l
  in aux l_var 0
;;
  

(* nom de l'extension *)
(* e : term de depart *)
(* n : nb de metas *)
let new_meta_mult ext e n =
  let l_new_var = do_new_var n in
  let rec do_list_meta i l_meta =
    (* print_int i; *)
    match i with
      |ii when ii=n -> l_meta
      |ii -> 
	do_list_meta 
	  (ii+1)
	  (l_meta@
	     [emeta(eapp(ext,[
	       eapp("mult",[e;
			    evar(string_of_int ii);
			    eapp("meta",(l_var_cour ii l_new_var l_meta))])]))])
  in do_list_meta 0 []
;;

(* let test1 = new_meta_mult "test" (evar("tessst")) 3;; *)
(* List.iter (fun x -> Print.expr (Print.Chan stdout) x;print_newline ()) test1;; *)

(* ext : nom de l'extension *)
(* metas : liste des metas gauche *)
(* e : membre gauche de la regle *)
(* a partir de la liste gauche de metas
   renvoie la liste des substitutions (mg,md) ou md est une
   meta multiple 
*)
let constr_subst ext metas e =
  List.combine 
    (List.map 
       (fun x->emeta(x)) metas) 
    (new_meta_mult ext e (List.length metas))
;;

(* ext : nom de l'extension *)
(* name : nom de la règle *)
(* a : membre gauche de la surrègle *)
(* b : membre droit de la surrègle *)
let ajout_newnode ext name a b =
  Hashtbl.add tb_branches name b;
  try
    let (new_newnodes,rang)=trouve_rang a !newnodes_mg in
    newnodes_mg:=new_newnodes;
    let mg = match_t a in
    let f_newnodes term g =
      try
	let unif = mg term ext in
	let new_a = substitute_3rd unif a in
	let unif_meta = 
	  match get_metas_branches b with
	    | [] -> []
	    | [m] -> [(emeta(m),emeta(eapp(ext,[new_a])))]
	    | l -> constr_subst ext l new_a
	in
	let unif = unif@unif_meta in
	let newbranches = substitute_branches unif b in 
	let args2 = List.map (fun x -> snd x) unif in
	let args = [term]@(List.concat newbranches)@args2 in
	mknode_item term Prop ext name args (Array.of_list newbranches) g
      with Non_unifiable -> []
    in 
    let t = find_extension ext !active in
    {t with newnodes = 
	fun e g l -> insere_rang_n (f_newnodes e g) rang (t.newnodes e g l)
    }
  with Non_insere -> find_extension ext !active
;;



(**************** make_inst  *****************)


let mknode m ext name args branches g =
  [ {
    nconc = [m];
    nrule = Mlproof.Ext (ext, name, args);
    nprio = (Inst m);
    ngoal = g;
    nbranches = branches;
  } ]
;;

let find_mg_rule a ext =
  List.find (fun x -> 
    try
      let _ =   match_t x a ext in
      true 
    with Non_unifiable -> false) !newnodes_mg ;;

let make_inst ext  =
  let f_make_inst m1 term g =
    match m1 with
      |Eapp (ext,[m],_) ->
	begin
	  try
	    let a = find_mg_rule m ext in
	    let (name,b) = Hashtbl.find rules a in
	    let metas = get_metas_branches b in
	    let m_a=
	      match metas with
		|[m] -> emeta(m)
		|_ -> assert false 	(* TO DO *)
	    in
	    let unif = (match_t a m ext)@[(m_a,term)] in
	    let newbranches = substitute_branches unif b in
	    let args2 = List.map (fun x -> snd x) unif in
	    let args = m::(List.concat newbranches)@args2 in
	    mknode m ext (name^"_inst") args (Array.of_list newbranches) g
	  with 
	    | Non_unifiable -> []
	    | Not_found -> assert false
	end
      |_ -> assert false (* TO DO : cas plusieurs métas*)
  in 
  let t = find_extension ext !active in
  {t with make_inst = 
      fun m term g -> f_make_inst m term g
  }
;;

(* to_llargs *)
(* ext : nom de l'extension *)
let to_llargs r ext =
  match r with
    | Mlproof.Ext (_,name,c::l) ->
      let rec aux li l_b l_b_res=
	match l_b with
	  |[] -> (ext^"_"^name,li,[c],l_b_res)
	  |l_1::l_n -> 
	    let rec parcours_branche b b_res li =
	      match b,li with
		|[],li -> (b_res,li)
		|h1::hn,h11::hnn ->
		  parcours_branche hn (b_res@[h11]) hnn
		|_ -> assert false
		
	    in 
	    let (b,lii) = (parcours_branche l_1 [] li) in
	    aux lii l_n (l_b_res@[b])
      in aux l (Hashtbl.find tb_branches name) []
    |_ -> assert false
;;

let print_llargs llargs =
  match llargs with
    |(name,li,[c],l_b) -> 
      print_string (name^" ");
      List.iter (fun x -> Print.expr_soft (Print.Chan stdout) x) li;
      Print.expr_soft (Print.Chan stdout) c;
      print_rule name (evar("a")) l_b
    |_ -> assert false;;
      
let to_llproof n_ext =
  let f_to_llproof tr_expr mlp args =
    match mlp.mlrule with
      | _ -> 
	let (name, meta, con, hyps) = to_llargs mlp.mlrule n_ext in
	print_llargs (name,meta,con,hyps);
	let tmeta = List.map tr_expr meta in
	let tcon = List.map tr_expr con in
	let thyps = List.map (List.map tr_expr) hyps in
	let (subs, exts) = List.split (Array.to_list args) in
	let ext = List.fold_left Expr.union [] exts in
	let extras = Expr.diff ext mlp.mlconc in
	let nn = {
          Llproof.conc = List.map tr_expr (List.rev_append extras mlp.mlconc);
          Llproof.rule = Llproof.Rextension (n_ext,name, tmeta, tcon, thyps);
          Llproof.hyps = subs;
	}
	in (nn, extras)
  in 
  let t = find_extension n_ext !active in
  {t with to_llproof = 
      fun tr_expr mlp args -> f_to_llproof tr_expr mlp args
  }
;;


(* mise à jour *)

let replace_ext name t_new =
  let rec aux th =
    match th with
      |[] -> assert false
      |t::q when t.name=name -> 
	  t_new::q
      |t::q -> 	t::(aux q)
  in 
  active:=aux !active;
  theories:=aux !theories
;;


let maj_newnode ext name a b =
  replace_ext 
    ext
    (ajout_newnode ext name a b)
;;

let maj_make_inst ext  =
  replace_ext 
    ext
    (make_inst ext )
;;

let maj_to_llproof ext =
  replace_ext 
    ext
    (to_llproof ext)
;;

let maj_all ext name a b =
  maj_newnode ext name a b;
  maj_make_inst ext;
;;
