(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
Version.add "$Id$";;

(* Extension for the B set theory. *)

open Printf;;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Phrase;;
open Print;;
open Lltocoq;;

let tb_meta : ((int,expr) Hashtbl.t)= Hashtbl.create 999997 ;;
let gen_int =
  let counter = ref 0 in
  fun () ->
    let res = !counter in
    begin
      incr counter;
      res
    end
;;

let add_formula e = ();;
let remove_formula e = ();;

let b_expr = [
  "B_cart_prod";
  "B_pow";
  "B_cup";
  "B_cap";
  "B_diff";
  "B_ext";
  "B_empty";
  "B_BIG";
  "B_pair";
  "B_inv";
  "B_dom";
  "B_ran";
  "B_comp";
  "B_id";
  "B_restg";
  "B_restd";
  "B_sustg";
  "B_sustd";
  "B_img";
  "B_over";
  "B_fct_p"
];;

let b_pred = [
  "B_eq";
  "B_in"
];;

let newmeta_B e  =  emeta (eapp ("B",[e])) ;;

let mknode prio name conc args branches g =
    [ {
      nconc = [conc];
      nrule = Ext ("B", name, args);
      nprio = prio;
      ngoal = g;
      nbranches = branches;
    } ]
;;


let mknode_item n = 
  match n with
    |[a] -> [ Node a ]
    |_ -> assert false;;

let mknode_inpow prio conc e1 e2 m g =
  let h1 = enot(eapp("B_in",[m;e1])) in
  let h2 = eapp("B_in",[m;e2]) in
  mknode prio "B_in_pow" conc [conc; h2; h1; e1; e2 ; m ]
    [| [h2]; [h1] |] g
;;

let mknode_notincartprod2 prio conc l_args l_meta g=
  match l_args,l_meta with
    |[e1;e2;e3],[y;z]->
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[y;z])])) and
	  h2 = enot(eapp("B_in",[y;e2])) and
	  h3 = enot(eapp("B_in",[z;e3])) in
      mknode prio "B_notin_cart_prod_2" conc
	[conc; h1; h2; h3; e1; e2; e3; y;z ] 	
	[| [h1];[h2];[h3] |] g
    |_ -> assert false
;;

let mknode_notininv prio conc l_args l_meta g =
  match l_args,l_meta with
    |[e1;e2],[y;z]-> 
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[y;z])])) and
	  h2 = enot(eapp("B_in",[eapp("B_pair",[z;y]);e2])) in
      mknode prio "B_notin_inv" conc [conc; h2; h1; e1; e2 ;y;z ] 
	[| [h2];[h1] |] g
    |_ -> assert false

;;

  
let mknode_notindom prio conc e1 e2 m g =
    let h = enot(eapp("B_in", [eapp ("B_pair", [e1;m]);e2])) in
    mknode prio "B_notin_dom" conc [conc; h; e1; e2; m ]
      [| [h] |] g
;;

let mknode_notinran prio conc e1 e2 m g =
   let h = enot(eapp("B_in", [eapp ("B_pair", [m;e1]);e2])) in
  mknode prio "B_notin_ran" conc [conc; h; e1; e2; m ]
    [| [h] |] g
;;

let mknode_pairnotincomp prio conc x z e2 e3 m g =
  let h1 = enot(eapp("B_in",[eapp("B_pair",[x;m]);e2]))
  and h2 = enot(eapp("B_in",[eapp("B_pair",[m;z]);e3])) in
  mknode prio "B_pair_notin_comp" conc 
    [conc; h1; h2; x; z; e2; e3; m ] 
    [| [h1] ; [h2] |] g
;;

let mknode_incomp prio conc e1 e2 e3 x y z g =
  let h1 = eapp("=",[e1;eapp("B_pair",[x;z])]) 
  and h2 = eapp("B_in",[eapp("B_pair",[x;y]);e2])
  and h3 = eapp("B_in",[eapp("B_pair",[y;z]);e3]) in
  mknode prio "B_in_comp" conc
    [conc; h1; h2; h3; e1; e2; e3 ] 
    [| [h1;h2;h3] |] g   
;;

let mknode_notincomp prio conc l_args l_meta g =
  match l_args,l_meta with
    |[e1;e2;e3],[x;y;z] ->
      Print.expr (Print.Chan stdout) x;
      Print.expr (Print.Chan stdout) y;
      Print.expr (Print.Chan stdout) z;
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[x;y])]))
      and h2 = enot(eapp("B_in",[eapp("B_pair",[x;z]);e2]))
      and h3 = enot(eapp("B_in",[eapp("B_pair",[z;y]);e3])) in
      mknode prio "B_notin_comp" conc 
	[conc; h1; h2; h3; e1; e2; e3; x; y;z ] 
	[| [h1]; [h2]; [h3] |] g
    |_ -> assert false
;;


let mknode_notinid prio conc e1 e2 m g =
  let h1 = enot(eapp("=",[e1;eapp("B_pair",[m;m])]))
  and h2 = enot(eapp("B_in",[m;e2])) in
  mknode prio "B_notin_id" conc [conc; h1; h2; e1; e2;m ]
    [| [h1]; [h2] |] g
;;

let mknode_notinrestg prio conc l_args l_meta g =
  match l_args,l_meta with
    |[e1;e2;e3],[x;y] -> 
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[x;y])])) 
      and h2 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e3]))
      and h3 = enot(eapp("B_in",[x;e2])) in
      mknode prio "B_notin_restg" conc [conc; h1; h2; h3; e1; e2; e3; x; y ] 
	[| [h1]; [h2]; [h3] |] g
    |_ -> assert false
;;

let mknode_notinrestd prio conc l_args l_meta g =
  match l_args,l_meta with
    |[e1;e2;e3],[x;y] -> 
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[x;y])])) 
      and h2 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e2]))
      and h3 = enot(eapp("B_in",[y;e3])) in
      mknode prio "B_notin_restd" conc [conc; h1; h2; h3; e1; e2; e3; x; y ] 
	[| [h1]; [h2]; [h3] |] g
    |_ -> assert false
;;

let mknode_notinsustg prio conc l_args l_meta g =
  match l_args,l_meta with
    |[e1;e2;e3],[x;y] ->
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[x;y])])) 
      and h2 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e3]))
      and h3 = eapp("B_in",[x;e2]) in
      mknode prio "B_notin_sustg" conc [conc; h1; h2; h3; e1; e2; e3; x; y ] 
	[| [h1]; [h2]; [h3] |] g
    |_ -> assert false
;;

let mknode_notinsustd prio conc l_args l_meta g =
  match l_args,l_meta with
    |[e1;e2;e3],[x;y] ->
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[x;y])])) 
      and h2 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e2]))
      and h3 = eapp("B_in",[y;e3]) in
      mknode prio "B_notin_sustd" conc [conc; h1; h2; h3; e1; e2; e3; x; y ] 
	[| [h1]; [h2]; [h3] |] g
    |_ -> assert false
;;

let mknode_notinimg prio conc e1 e2 e3 m g =
  let h1 = enot(eapp("B_in",[m;e3]))
  and h2 = enot(eapp("B_in",[eapp("B_pair",[m;e1]);e2])) in
  mknode prio "B_notin_img" conc [conc; h1; h2; e1; e2; e3; m ]
    [| [h1];[h2] |] g
;;

let mknode_pairinover prio conc x y e3 e4 m g =
  let h1 = eapp("B_in",[eapp("B_pair",[x;y]);e3])
  and h2 = enot(eapp("B_in",[eapp("B_pair",[x;m]);e4]))
  and h3 = eapp("B_in",[eapp("B_pair",[x;y]);e4]) in
  mknode prio "B_pair_in_over" conc 
    [conc; h1; h2; h3; x; y; e3; e4; m ]
    [| [h1;h2]; [h3] |] g
;;

let mknode_inover prio conc x e3 e4 l  g =
  match l with
    |[m;tau_y;tau_z] ->
      let h1 = eapp("=",[x;eapp("B_pair",[tau_y;tau_z])])
      and h2 = eapp("B_in",[eapp("B_pair",[tau_y;tau_z]);e3])
      and h3 = enot(eapp("B_in",[eapp("B_pair",[tau_y;m]);e4]))
      and h4 = eapp("B_in",[eapp("B_pair",[tau_y;tau_z]);e4]) in
      mknode prio "B_in_over" conc 
	[conc; h1; h2; h3; h4; x; e3; e4; m ]
	[| [h1;h2;h3]; [h1;h4] |] g
    |_ -> assert false
;;

let mknode_notinover prio conc x e3 e4 l g =
  match l with
    |[y;z;tau] ->
      let h1 = enot(eapp("=",[x;eapp("B_pair",[y;z])]))
      and h2 = enot(eapp("B_in",[eapp("B_pair",[y;z]);e3]))
      and h3 = enot(eapp("B_in",[eapp("B_pair",[y;z]);e4]))
      and h4 = eapp("B_in",[eapp("B_pair",[y;tau]);e4]) in
      mknode prio "B_notin_over" conc 
	[conc; h1; h2; h3; h4; x; e3; e4; y; z]
	[| [h1]; [h2;h3]; [h4;h3] |] g
    |_ -> assert false
;;

let mknode_infctp prio conc e1 e2 e3 x y z g =
  let (* h0 = enot(eapp("B_in",[e1;eapp("B_pow",[e2;e3])]))  *)
    (* and h1 = enot(eapp("B_in",[x;e2])) *)
    (* and h2 = enot(eapp("B_in",[y;e3])) *)
    (* and h3 = enot(eapp("B_in",[z;e3])) *)
    (* and *) h4 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e1]))
  and h5 = enot(eapp("B_in",[eapp("B_pair",[x;z]);e1]))
  and h6 = eapp("=",[y;z]) in
  mknode prio "B_in_fct_p" conc 
    [conc; (* h0; h1; h2; h3; *) h4; h5; h6; e1; e2; e3; x; y; z ]
    [| (* [h0]; [h1]; [h2]; [h3]; *) [h4]; [h5]; [h6] |] g
;;

let mknode_paireq2 prio conc e1 e3 e4 l_m g =
  match l_m with
    |[y;z] ->
      let h1 = enot(eapp("=",[e1;eapp("B_pair",[y;z])]))
      and h2 = eapp("=",[e3;y])
      and h3 = eapp("=",[e4;z]) in
      mknode prio "B_pair_eq_2" conc 
	[conc; h1; h2; h3; e1; e3; e4; y; z]
	[| [h1];[h2;h3] |] g
    |_ -> assert false
;;

let mknode_eq prio conc e1 e2 m g =
  let m_in_e1 = eapp ("B_in", [m; e1]) in
  let m_in_e2 = eapp ("B_in", [m; e2]) in
  let h1 = enot m_in_e1 in
  let h2 = enot m_in_e2 in
  let h3 = m_in_e1 in
  let h4 = m_in_e2 in
  mknode prio "B_eq" conc [conc; h1; h2; h3; h4; e1; e2; m]
    [| [h1;h2]; [h3;h4] |] g
;;

let newnodes_prop e g =
  let mknode prio name args branches =
    [ Node {
      nconc = [e];
      nrule = Ext ("B", name, args);
      nprio = prio;
      ngoal = g;
      nbranches = branches;
    } ]
  in
  match e with
   (* puissance *)
    | Eapp ("B_in", [e1;Eapp("B_pow",[e2],_)],_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_inpow Prop e e1 e2 meta g)
    | Enot (Eapp ("B_in", [e1;Eapp("B_pow",[e2],_)],_),_) ->
      let x = newvar() in
      let f = enot(eimply(eapp("B_in",[x;e1]),eapp("B_in",[x;e2]))) in
      let tau = etau(x,Namespace.univ_name,f) in
      let h1 = eapp ("B_in", [tau; e1]) in
      let h2 = enot (eapp ("B_in", [tau; e2])) in
      (mknode Prop "B_notin_pow" [e; h1; h2; e1; e2] [| [h1;h2] |])
    (* cart_prod pair *)
    | Eapp ("B_in", [Eapp("B_pair", [e1; e2], _);
		     Eapp("B_cart_prod", [e3; e4], _)], _) ->
      let h1 = eapp ("B_in", [e1; e3]) in
      let h2 = eapp ("B_in", [e2; e4]) in
      mknode Prop "B_in_cart_prod" [e; h1; h2; e1; e2; e3; e4] [| [h1;h2] |]
    | Enot (Eapp ("B_in", [Eapp("B_pair", [e1; e2], _);
			   Eapp("B_cart_prod", [e3; e4], _)], _),_) ->
      let h1 = enot(eapp ("B_in", [e1; e3])) in
      let h2 = enot(eapp ("B_in", [e2; e4])) in
      mknode Prop "B_notin_cart_prod" [e; h1; h2; e1; e2; e3; e4] [| [h1] ; [h2] |]
    (* cart_prod gen *)
    | Eapp ("B_in", [e1;Eapp ("B_cart_prod",[e2;e3],_)],_) ->
      let y = newvar() and
  	  z = newvar() in
      let fy = eex(z,
  		   Namespace.univ_name,
  		   eand(eapp("=",[e1;eapp("B_pair",[y;z])]),
  			eand(eapp("B_in",[y;e2]),
			     eapp("B_in",[z;e3])))) in
      let tau_y = etau(y,Namespace.univ_name,fy) in
      let fz =  eand(eapp("=",[e1;eapp("B_pair",[tau_y;z])]),
  		     eand(eapp("B_in",[tau_y;e2]),
			  eapp("B_in",[z;e3]))) in
      let tau_z = etau(z,Namespace.univ_name,fz) in
      let h1 = eapp("=",[e1;eapp("B_pair",[tau_y;tau_z])])
      and h2 = eapp("B_in",[tau_y;e2])
      and h3 = eapp("B_in",[tau_z;e3]) in
      mknode Prop "B_in_cart_prod_2" [e; h1; h2; h3; e1; e2; e3 ] 
	[| [h1;h2;h3] |]
    | Enot(Eapp ("B_in", [e1;Eapp ("B_cart_prod",l_args,_)],_),_) ->
      let x = newvar() 
      and y = newvar() in
      let mx = newmeta_B (eapp("mult",[e;
				       evar("0");
				       eapp("meta",[x;y])])) in
      let my = newmeta_B (eapp("mult",[e;
				       evar("1");
				       eapp("meta",[mx;y])])) in
       mknode_item (mknode_notincartprod2 Prop e (e1::l_args) [mx;my] g)
    (* egalité entre 2 paires *)
    | Eapp ("=", [Eapp("B_pair", [e1; e2], _);
		  Eapp("B_pair", [e3; e4], _)], _) ->
      let h1 = eapp ("=", [e1; e3]) in
      let h2 = eapp ("=", [e2; e4]) in
      mknode Prop "B_pair_eq" [e; h1; h2; e1; e2; e3; e4] [| [h1;h2] |]
    (* Union *)
    | Eapp ("B_in", [e1; Eapp ("B_cup", [e2; e3], _)], _) ->
      let h1 = eapp ("B_in", [e1; e2]) in
      let h2 = eapp ("B_in", [e1; e3]) in
      mknode Prop "B_in_cup" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]
    | Enot (Eapp ("B_in", [e1; Eapp ("B_cup", [e2; e3], _)], _), _) ->
      let h1 = enot (eapp ("B_in", [e1; e2])) in
      let h2 = enot (eapp ("B_in", [e1; e3])) in
      mknode Prop "B_notin_cup" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]
    (* Intersection *)
    | Eapp ("B_in", [e1; Eapp ("B_cap", [e2; e3], _)], _) ->
      let h1 = eapp ("B_in", [e1; e2]) in
      let h2 = eapp ("B_in", [e1; e3]) in
      mknode Prop "B_in_cap" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]
    | Enot (Eapp ("B_in", [e1; Eapp ("B_cap", [e2; e3], _)], _), _) ->
      let h1 = enot (eapp ("B_in", [e1; e2])) in
      let h2 = enot (eapp ("B_in", [e1; e3])) in
      mknode Prop "B_notin_cap" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]
    (* Différence *)
    | Eapp ("B_in", [e1; Eapp ("B_diff", [e2; e3], _)], _) ->
      let h1 = eapp ("B_in", [e1; e2]) in
      let h2 = enot (eapp ("B_in", [e1; e3])) in
      mknode Prop "B_in_diff" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]
    | Enot (Eapp ("B_in", [e1; Eapp ("B_diff", [e2; e3], _)], _), _) ->
      let h1 = enot (eapp ("B_in", [e1; e2])) in
      let h2 = eapp ("B_in", [e1; e3]) in
      mknode Prop "B_notin_diff" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]
    (* Ensemble en extension *)
    | Eapp ("B_in", [e1; Eapp ("B_ext", [e2], _)], _) ->
      let h = eapp ("=", [e1; e2]) in
      mknode Prop "B_in_ext" [e; h; e1; e2] [| [h] |]
    | Enot (Eapp ("B_in", [e1; Eapp ("B_ext", [e2], _)], _), _) ->
      let h = enot (eapp ("=", [e1; e2])) in
      mknode Prop "B_notin_ext" [e; h; e1; e2] [| [h] |]
    (* Ensemble vide *)
    | Eapp ("B_in", [e1; Evar ("B_empty",_)], _) ->
      let h1 = eapp ("B_in", [e1; eapp("B_BIG",[])]) in
      let h2 = enot (h1) in
      mknode Prop "B_in_empty" [e; h1; h2; e1] [| [h1; h2] |]
    (* Inverse pair *)
    | Eapp ("B_in", [Eapp ("B_pair",[e1;e2],_); Eapp ("B_inv", [e3], _)], _) ->
      let h = eapp ("B_in", [eapp("B_pair",[e2;e1]);e3]) in
      mknode Prop "B_pair_in_inv" [e; h; e1; e2; e3] [| [h] |]
    | Enot (Eapp ("B_in", 
		  [Eapp("B_pair",[e1;e2],_); 
		   Eapp ("B_inv", [e3], _)],_),_) ->
      let h = enot(eapp ("B_in",[eapp("B_pair",[e2;e1]);e3])) in
      mknode Prop "B_pair_notin_inv" [e; h; e1; e2; e3] [| [h] |]
    (* Inverse gen *)
    | Eapp ("B_in", [e1; Eapp ("B_inv", [e2], _)], _) ->
      let y = newvar() and
    	  z = newvar() in
      let fy = eex(z,Namespace.univ_name,
  		   eand(
  		     eapp("=",[e1;eapp("B_pair",[y;z])]),
    		     eapp("B_in",[eapp("B_pair",[z;y]);e2]))) in
      let tau_y = etau(y,Namespace.univ_name,fy) in
      let fz =
	eand(
  	  eapp("=",[e1;eapp("B_pair",[tau_y;z])]),
  	  eapp("B_in",[eapp("B_pair",[z;tau_y]);e2])) in
      let tau_z = etau(z,Namespace.univ_name,fz) in
      let h1 = eapp ("=", [e1;eapp("B_pair",[tau_y;tau_z])]) in
      let h2 = eapp ("B_in", [eapp("B_pair",[tau_z;tau_y]);e2]) in
      mknode Prop "B_in_inv" [e; h1; h2; e1; e2 ] [| [h1 ; h2] |]
    | Enot(Eapp ("B_in", [e1; Eapp ("B_inv", [e2], _)], _),_) ->

      let x = newvar()
      and y = newvar() in
      let mx = newmeta_B (eapp("mult",[e;
				       evar("0");
				       eapp("meta",[x;y])])) in
      let my = newmeta_B (eapp("mult",[e;
				       evar("1");
				       eapp("meta",[mx;y])])) in
      mknode_item (mknode_notininv Prop e [e1;e2] [mx;my] g)
    (* Domaine *)
    | Eapp ("B_in", [e1; Eapp ("B_dom", [e2], _)], _) ->
      let x = newvar() in
      let f = eapp("B_in", [eapp ("B_pair", [e1;x]);e2]) in
      let tau = etau(x,Namespace.univ_name,f) in
      let h = eapp("B_in", [eapp ("B_pair", [e1;tau]);e2]) in
      mknode Prop "B_in_dom" [e; h; e1; e2]
	[| [h] |]
    | Enot(Eapp ("B_in", [e1; Eapp ("B_dom", [e2], _)], _),_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_notindom Prop e e1 e2 meta g)
   (* Range *)
    | Eapp ("B_in", [e1; Eapp ("B_ran", [e2], _)], _) ->
      let x = newvar() in
      let f = eapp("B_in", [eapp ("B_pair", [x;e1]);e2]) in
      let tau = etau(x,Namespace.univ_name,f) in
      let h = eapp("B_in", [eapp ("B_pair", [tau;e1]);e2]) in
      mknode Prop "B_in_ran" [e; h; e1; e2]
	[| [h] |]
    | Enot(Eapp ("B_in", [e1; Eapp ("B_ran", [e2], _)], _),_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_notinran Prop e e1 e2 meta g)
   (* Composition pair*)
    | Eapp ("B_in", [Eapp("B_pair",[x;z],_); 
		     Eapp ("B_comp", [e2;e3], _)], _) ->
      let y = newvar() in
      let f = 
	eand(
	  eapp("B_in",[eapp("B_pair",[x;y]);e2]),
	  eapp("B_in",[eapp("B_pair",[y;z]);e3])) in
      let tau = etau(y,Namespace.univ_name,f) in
      let h1 = eapp("B_in",[eapp("B_pair",[x;tau]);e2])
      and h2 = eapp("B_in",[eapp("B_pair",[tau;z]);e3]) in
      mknode Prop "B_pair_in_comp" [e; h1; h2; x; z; e2; e3 ] 
	[| [h1;h2] |]
    | Enot (Eapp ("B_in", [Eapp("B_pair",[x;z],_); 
			   Eapp ("B_comp", [e2;e3], _)],_),_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_pairnotincomp Prop e x z e2 e3 meta g)
   (* Composition gen *)
    | Eapp ("B_in", [e1; Eapp ("B_comp", [e2;e3], _)],_) ->
      let x = newvar() and
	  y = newvar() and
	  z = newvar() in
      let fx = 
	eex(z,Namespace.univ_name,
    	    eand(eapp("=",[e1;eapp("B_pair",[x;z])]),
		 eex(y,Namespace.univ_name,
    		     eand(eapp("B_in",[eapp("B_pair",[x;y]);e2]),
			  eapp("B_in",[eapp("B_pair",[y;z]);e3])))))
      in
      let taux = etau(x,Namespace.univ_name,fx) in
      let fz =
	eand(eapp("=",[e1;eapp("B_pair",[taux;z])]),
	     eex(y,Namespace.univ_name,
    		 eand(eapp("B_in",[eapp("B_pair",[taux;y]);e2]),
		      eapp("B_in",[eapp("B_pair",[y;z]);e3])))) in
      let tauz = etau(z,Namespace.univ_name,fz) in
      let fy =
	eand(eapp("B_in",[eapp("B_pair",[taux;y]);e2]),
	     eapp("B_in",[eapp("B_pair",[y;tauz]);e3])) in
      let tauy = etau(y,Namespace.univ_name,fy) in

      mknode_item (mknode_incomp Prop e e1 e2 e3 taux tauy tauz g)
   
    | Enot(Eapp ("B_in", [e1; Eapp ("B_comp", l_args, _)], _),_) -> 
      (* print_string "dans not comp\n"; *)
      let x = newvar()
      and y = newvar()
      and z = newvar() in
      let mx = newmeta_B (eapp("mult",[e;
				       evar("0");
				       eapp("meta",[x;y;z])])) in
      let my = newmeta_B (eapp("mult",[e;
				       evar("1");
				       eapp("meta",[mx;y;z])])) in
      let mz = newmeta_B (eapp("mult",[e;
				       evar("2");
				       eapp("meta",[mx;my;z])])) in
      mknode_item (mknode_notincomp Prop e (e1::l_args) [mx;my;mz] g)
  
    (* Identité pair *)
    | Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_id", [e2], _)], _) ->
      let h1 = eapp("=",[x;y])
      and h2 = eapp("B_in",[x;e2]) in
      mknode Prop "B_pair_in_id" [e; h1;h2; x; y; e2 ] [| [h1; h2] |]
    | Enot(Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_id", [e2], _)], _),_) ->
      let h1 = enot(eapp("=",[x;y]))
      and h2 = enot(eapp("B_in",[x;e2])) in
      mknode Prop "B_pair_notin_id" [e; h1; h2; x; y; e2 ] [| [h1] ; [h2] |]
    (* Identité gen *)
    | Eapp ("B_in", [e1; Eapp ("B_id", [e2], _)], _) ->
      let x = newvar() in
      let f = eand(
	eapp("=",[e1;eapp("B_pair",[x;x])]),
	eapp("B_in",[x;e2])) in
      let taux = etau(x,Namespace.univ_name,f) in
      let h1 = eapp("=",[e1;eapp("B_pair",[taux;taux])])
      and h2 = eapp("B_in",[taux;e2]) in
      mknode Prop "B_in_id" [e; h1; h2; e1; e2 ] [| [h1; h2] |]
    | Enot (Eapp ("B_in", [e1; Eapp ("B_id", [e2], _)],_),_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_notinid Prop e e1 e2 meta g)
  (* | Eapp ("B_in", [e1; Eapp ("B_id", [e2], _)], _) -> *)
  (*   let x = newvar() in *)
  (*   let y = newvar() in *)
  (*   let fx = *)
  (*     eex(y,Namespace.univ_name, *)
  (* 	  eand( *)
  (* 	    eand( *)
  (* 	      eand( *)
  (* 		eapp("=",[e1;eapp("B_pair",[x;y])]), *)
  (* 		eapp("=",[x;y])), *)
  (* 	      eapp("B_in",[x;e2])), *)
  (* 	    eapp("B_in",[y;e2]))) in *)
  (*   let taux = etau(x,Namespace.univ_name,fx) in *)
  (*   let fy = *)
  (*     eand( *)
  (* 	eand( *)
  (* 	  eand( *)
  (* 	    eapp("=",[e1;eapp("B_pair",[taux;y])]), *)
  (* 	    eapp("=",[taux;y])), *)
  (* 	  eapp("B_in",[taux;e2])), *)
  (* 	eapp("B_in",[y;e2])) in *)
  (*   let tauy = etau(y,Namespace.univ_name,fy) in *)
  (*   let h1 = eapp("=",[e1;eapp("B_pair",[taux;tauy])]) *)
  (*   and h2 = eapp("=",[taux;tauy]) *)
  (*   and h3 = eapp("B_in",[taux;e2]) *)
  (*   and h4 = eapp("B_in",[tauy;e2]) in *)
  (*   mknode Prop "B_in_id" [e; h1; h2; h3; h4; e1; e2 ] [| [h1; h2; h3; h4] |] *)
  (* | Enot (Eapp ("B_in", [e1; Eapp ("B_id", [e2], _)],_),_) -> *)
  (*   let kx = gen_int () *)
  (*   and ky = gen_int () in *)
  (*   let x = emeta(eapp("$B_mult_meta", *)
  (* 		       [evar("0");e; *)
  (* 			evar(string_of_int(kx)); *)
  (* 			evar(string_of_int(ky))]))  *)
  (*   and y = emeta(eapp("$B_mult_meta", *)
  (* 		       [evar("1");e; *)
  (* 			evar(string_of_int(kx)); *)
  (* 			evar(string_of_int(ky))])) in *)
  (*   Hashtbl.add tb_meta kx x; *)
  (*   Hashtbl.add tb_meta ky y; *)
  (*   let h1 = enot(eapp("=",[e1;eapp("B_pair",[x;y])])) *)
  (*   and h2 = enot(eapp("=",[x;y])) *)
  (*   and h3 = enot(eapp("B_in",[x;e2])) *)
  (*   and h4 = enot(eapp("B_in",[y;e2])) in *)
  (*   mknode Prop "B_notin_id" [e; h1; h2; h3; h4; e1; e2; x; y ] *)
  (*     [| [h1]; [h2]; [h3]; [h4] |] *)
    (* Restriction gauche pair *)
    | Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_restg", [e2;e3], _)], _) ->
      let h1 = eapp("B_in",[eapp("B_pair",[x;y]);e3])
      and h2 = eapp("B_in",[x;e2]) in
      mknode Prop "B_pair_in_restg" [e; h1;h2; x; y; e2; e3 ] [| [h1;h2] |]
    | Enot(Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_restg", [e2;e3], _)], _),_) ->
      let h1 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e3]))
      and h2 = enot(eapp("B_in",[x;e2])) in
      mknode Prop "B_pair_notin_restg" [e; h1; h2; x; y; e2; e3 ] 
	[| [h1]; [h2] |]
    (* Restriction gauche gen *)
    | Eapp ("B_in", [e1; Eapp ("B_restg", [e2;e3], _)], _) ->
      let x = newvar()
      and y = newvar() in
      let fx =
	eex(y,Namespace.univ_name,
    	    eand(eapp("=",[e1;eapp("B_pair",[x;y])]),
		 eand(eapp("B_in",[e1;e3]),
		      eapp("B_in",[x;e2])))) in
      let taux = etau(x,Namespace.univ_name,fx) in
      let fy = 
	eand(eapp("=",[e1;eapp("B_pair",[taux;y])]),
	     eand(eapp("B_in",[e1;e3]),
		  eapp("B_in",[taux;e2]))) in
      let tauy = etau(y,Namespace.univ_name,fy) in
      let h1 = eapp("=",[e1;eapp("B_pair",[taux;tauy])]) 
      and h2 = eapp("B_in",[eapp("B_pair",[taux;tauy]);e3])
      and h3 = eapp("B_in",[taux;e2]) in
      mknode Prop "B_in_restg" [e; h1;h2;h3; e1; e2; e3 ] [| [h1;h2;h3] |]
    | Enot( Eapp ("B_in", [e1; Eapp ("B_restg", l_args, _)], _),_) ->   
      let x = newvar() and
	  y = newvar() in
      let mx = newmeta_B (eapp("mult",[e;evar("0");
				       eapp("meta",[x;y])])) in
      let my = newmeta_B (eapp("mult",[e;evar("1");
				       eapp("meta",[mx;y])])) in
      mknode_item (mknode_notinrestg Prop e (e1::l_args) [mx;my] g)

    (* Restriction droite pair *)
    | Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_restd", [e2;e3], _)], _) ->
      let h1 = eapp("B_in",[eapp("B_pair",[x;y]);e2])
      and h2 = eapp("B_in",[y;e3]) in
      mknode Prop "B_pair_in_restd" [e; h1;h2; x; y; e2; e3 ] [| [h1;h2] |]
    | Enot(Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_restd", [e2;e3], _)], _),_) ->
      let h1 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e2]))
      and h2 = enot(eapp("B_in",[y;e3])) in
      mknode Prop "B_pair_notin_restd" [e; h1; h2; x; y; e2; e3 ] 
	[| [h1]; [h2] |]
    (* Restriction droite gen *)
    | Eapp ("B_in", [e1; Eapp ("B_restd", [e2;e3], _)], _) ->
      let x = newvar()
      and y = newvar() in
      let fx =
	eex(y,Namespace.univ_name,
    	    eand(eapp("=",[e1;eapp("B_pair",[x;y])]),
		 eand(eapp("B_in",[e1;e2]),
		      eapp("B_in",[y;e3])))) in
      let taux = etau(x,Namespace.univ_name,fx) in
      let fy = 
	eand(eapp("=",[e1;eapp("B_pair",[taux;y])]),
	     eand(eapp("B_in",[e1;e2]),
		  eapp("B_in",[y;e2]))) in
      let tauy = etau(y,Namespace.univ_name,fy) in
      let h1 = eapp("=",[e1;eapp("B_pair",[taux;tauy])]) 
      and h2 = eapp("B_in",[eapp("B_pair",[taux;tauy]);e2])
      and h3 = eapp("B_in",[tauy;e3]) in
      mknode Prop "B_in_restd" [e; h1; h2; h3; e1; e2; e3 ] 
	[| [h1;h2;h3] |]
    | Enot( Eapp ("B_in", [e1; Eapp ("B_restd", l_args, _)], _),_) ->   
      let x = newvar() and
	  y = newvar() in
      let mx = newmeta_B (eapp("mult",[e;evar("0");
			   eapp("meta",[x;y])])) in
      let my = newmeta_B (eapp("mult",[e;evar("1");
			   eapp("meta",[mx;y])])) in
      mknode_item (mknode_notinrestd Prop e (e1::l_args) [mx;my] g)
	
    (* Soustraction gauche pair *)
    | Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_sustg", [e2;e3], _)], _) ->
      let h1 = eapp("B_in",[eapp("B_pair",[x;y]);e3])
      and h2 = enot(eapp("B_in",[x;e2])) in
      mknode Prop "B_pair_in_sustg" [e; h1;h2; x; y; e2; e3 ] [| [h1;h2] |]
    | Enot(Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_sustg", [e2;e3], _)], _),_) ->
      let h1 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e3]))
      and h2 = eapp("B_in",[x;e2]) in
      mknode Prop "B_pair_notin_sustg" [e; h1; h2; x; y; e2; e3 ] 
	[| [h1]; [h2] |]
    (* Soustraction gauche gen *)
    | Eapp ("B_in", [e1; Eapp ("B_sustg", [e2;e3], _)], _) ->
      let x = newvar()
      and y = newvar() in
      let fx =
	eex(y,Namespace.univ_name,
    	    eand(eapp("=",[e1;eapp("B_pair",[x;y])]),
		 eand(eapp("B_in",[e1;e3]),
		      eapp("B_in",[x;e2])))) in
      let taux = etau(x,Namespace.univ_name,fx) in
      let fy = 
	eand(eapp("=",[e1;eapp("B_pair",[taux;y])]),
	     eand(eapp("B_in",[e1;e3]),
		  eapp("B_in",[taux;e2]))) in
      let tauy = etau(y,Namespace.univ_name,fy) in
      let h1 = eapp("=",[e1;eapp("B_pair",[taux;tauy])]) 
      and h2 = eapp("B_in",[eapp("B_pair",[taux;tauy]);e3])
      and h3 = enot(eapp("B_in",[taux;e2])) in
      mknode Prop "B_in_sustg" [e; h1;h2;h3; e1; e2; e3 ] [| [h1;h2;h3] |]
    | Enot( Eapp ("B_in", [e1; Eapp ("B_sustg", l_args, _)], _),_) ->   
      let x = newvar() and
	  y = newvar() in
      let mx = newmeta_B (eapp("mult",[e;evar("0");
				       eapp("meta",[x;y])])) in
      let my = newmeta_B (eapp("mult",[e;evar("1");
				       eapp("meta",[mx;y])])) in
      mknode_item (mknode_notinsustg Prop e (e1::l_args) [mx;my] g)

    (* Soustraction droite pair*)
    | Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_sustd", [e2;e3], _)], _) ->
      let h1 = eapp("B_in",[eapp("B_pair",[x;y]);e2])
      and h2 = enot(eapp("B_in",[y;e3])) in
      mknode Prop "B_pair_in_sustd" [e; h1;h2; x; y; e2; e3 ] [| [h1;h2] |]
    | Enot(Eapp ("B_in", [Eapp("B_pair",[x;y],_); Eapp ("B_sustd", [e2;e3], _)], _),_) ->
      let h1 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e2]))
      and h2 = eapp("B_in",[y;e3]) in
      mknode Prop "B_pair_notin_sustd" [e; h1; h2; x; y; e2; e3 ] 
	[| [h1]; [h2] |]
    (* Soustraction droite pair*)
    | Eapp ("B_in", [e1; Eapp ("B_sustd", [e2;e3], _)], _) ->
      let x = newvar()
      and y = newvar() in
      let fx =
	eex(y,Namespace.univ_name,
    	    eand(eapp("=",[e1;eapp("B_pair",[x;y])]),
		 eand(eapp("B_in",[e1;e2]),
		      eapp("B_in",[y;e3])))) in
      let taux = etau(x,Namespace.univ_name,fx) in
      let fy = 
	eand(eapp("=",[e1;eapp("B_pair",[taux;y])]),
	     eand(eapp("B_in",[e1;e2]),
		  eapp("B_in",[y;e2]))) in
      let tauy = etau(y,Namespace.univ_name,fy) in
      let h1 = eapp("=",[e1;eapp("B_pair",[taux;tauy])]) 
      and h2 = eapp("B_in",[eapp("B_pair",[taux;tauy]);e2])
      and h3 = enot(eapp("B_in",[tauy;e3])) in
      mknode Prop "B_in_sustd" [e; h1; h2; h3; e1; e2; e3 ] 
	[| [h1;h2;h3] |]
    | Enot( Eapp ("B_in", [e1; Eapp ("B_sustd", l_args, _)], _),_) ->   
      let x = newvar() and
	  y = newvar() in
      let mx = newmeta_B (eapp("mult",[e;evar("0");
				       eapp("meta",[x;y])])) in
      let my = newmeta_B (eapp("mult",[e;evar("1");
				       eapp("meta",[mx;y])])) in
      mknode_item (mknode_notinsustd Prop e (e1::l_args) [mx;my] g)
    (* Image *)
    | Eapp ("B_in", [e1;Eapp("B_img",[e2;e3],_)],_) ->
      let x = newvar() in
      let f = eand(eapp("B_in",[x;e3]),eapp("B_in",[eapp("B_pair",[x;e1]);e2])) in

      let taux = etau(x,Namespace.univ_name,f) in
      let h1 = eapp("B_in",[taux;e3])
      and h2 = eapp("B_in",[eapp("B_pair",[taux;e1]);e2]) in
      mknode Prop "B_in_img" [e; h1; h2; e1; e2; e3 ]
	[| [h1;h2] |]
    | Enot (Eapp ("B_in", [e1;Eapp("B_img",[e2;e3],_)],_),_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_notinimg Prop e e1 e2 e3 meta g)
    (* Overide pair *)
    | Eapp ("B_in", [Eapp("B_pair",[x;y],_);Eapp("B_over",[e3;e4],_)],_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_pairinover Prop e x y e3 e4 meta g)
    | Enot (Eapp ("B_in",[Eapp("B_pair",[x;y],_);Eapp("B_over",[e3;e4],_)],_),_) ->
      let t = newvar() in
      let f = eapp("B_in", [eapp ("B_pair", [x;t]);e4]) in
      let taut = etau(t,Namespace.univ_name,f) in
      let h1 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e3]))
      and h2 = enot(eapp("B_in",[eapp("B_pair",[x;y]);e4]))
      and h3 = eapp("B_in",[eapp("B_pair",[x;taut]);e4])
      in
      mknode Prop "B_pair_notin_over" [e; h1; h2;h3; x; y; e3; e4 ]
	[| [h1;h2];[h3;h2] |]
    (* Overide gen *)
    | Eapp ("B_in", [x;Eapp("B_over",[e3;e4],_)],_) ->
      let y = newvar()
      and z = newvar()
      and t = newvar() in
      let fy = 
	eex(z,Namespace.univ_name,
  	    eand(eapp("=",[x;eapp("B_pair",[y;z])]),
  		 eor(
  		   eand(eapp("B_in",[eapp("B_pair",[y;z]);e3]),
  			enot(eex(t,Namespace.univ_name,
				 eapp("B_in",[eapp("B_pair",[y;t]);e4])))),
		   eapp("B_in",[eapp("B_pair",[y;z]);e4])))) in
      let tau_y = etau(y,Namespace.univ_name,fy) in
      let fz =  eand(eapp("=",[x;eapp("B_pair",[tau_y;z])]),
  		     eor(
  		       eand(eapp("B_in",[eapp("B_pair",[tau_y;z]);e3]),
  			    enot(eex(t,Namespace.univ_name,
				     eapp("B_in",[eapp("B_pair",[tau_y;t]);e4])))),
		       eapp("B_in",[eapp("B_pair",[tau_y;z]);e4]))) in
      let tau_z = etau(z,Namespace.univ_name,fz) in
      let meta = newmeta_B (eapp("mult",[e;tau_y;tau_z])) in
      mknode_item (mknode_inover Prop e x e3 e4 [meta;tau_y;tau_z] g)
    | Enot (Eapp ("B_in",[x;Eapp("B_over",[e3;e4],_)],_),_) ->
      let t = newvar()
      and y = newvar()
      and z = newvar() in
      let ft y = eapp("B_in", [eapp ("B_pair", [y;t]);e4]) in
      let tau y= etau(t,Namespace.univ_name,ft y) in
      let my = 
	newmeta_B (eapp("mult",[e;evar("0");
			   eapp("meta",[y;z]);
			   eapp("tau",[tau y])])) in
      let mz = 
	newmeta_B (eapp("mult",[e;evar("1");
			   eapp("meta",[my;z]);
			   eapp("tau",[tau my])])) in
      mknode_item (mknode_notinover Prop e x e3 e4 [my;mz;tau my] g)

    (* Fonction partielle *)
    (* TODO : A verifier *)

    (* |Eapp ("B_in",[r; Eapp ("B_fct_p",[s; t] ,_)] ,_) -> *)
    (*   let v1 = newvar() in  *)
    (*   let v2 = newvar() in  *)
    (*   let v3 = newvar() in  *)
    (*   let v4 = newvar() in  *)
    (*   let m1 = emeta(eapp("B",[eapp("mult",[e;evar("1");eapp("meta",[v1;v2;v3;v4])])])) in  *)
    (*   let m2 = emeta(eapp("B",[eapp("mult",[e;evar("2");eapp("meta",[m1;v2;v3;v4])])])) in  *)
    (*   let m3 = emeta(eapp("B",[eapp("mult",[e;evar("3");eapp("meta",[m1;m2;v3;v4])])])) in  *)
    (*   let m4 = emeta(eapp("B",[eapp("mult",[e;evar("4");eapp("meta",[m1;m2;m3;v4])])])) in  *)
    (*   let h1 = eapp ("=",[m4; m3]) in  *)
    (*   let h2 = enot (eapp ("B_in",[m2; r])) in  *)
    (*   let h3 = enot (eapp ("B_in",[m2; r])) in  *)
    (*   let h4 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m4]); r])) in  *)
    (*   let h5 = enot (eapp ("B_in",[m2; r])) in  *)
    (*   let h6 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m3]); r])) in  *)
    (*   let h7 = eapp ("=",[m4; m3]) in  *)
    (*   let h8 = eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])])))])]) in  *)
    (*   let h9 = eapp ("B_in",[etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])]))); t]) in  *)
    (*   let h10 = eapp ("B_in",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); s]) in  *)
    (*   let h11 = eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])])))])]) in  *)
    (*   let h12 = eapp ("B_in",[etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])]))); t]) in  *)
    (*   let h13 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m4]); r])) in  *)
    (*   let h14 = eapp ("B_in",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); s]) in  *)
    (*   let h15 = eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])])))])]) in  *)
    (*   let h16 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m3]); r])) in  *)
    (*   let h17 = eapp ("B_in",[etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])]))); t]) in  *)
    (*   let h18 = eapp ("B_in",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); s]) in  *)
    (*   mknode Prop "fonc_part" [e;h1;h2;h3;h4;h5;h6;h7;h8;h9;h10;h11;h12;h13;h14;h15;h16;h17;h18;r;s;t;m1;m2;m3;m4] [|[h1;h2];[h3;h4];[h5;h6];[h7;h8;h9;h10];[h11;h12;h13;h14];[h15;h16;h17;h18]|] *)



    (*  | Enot (Eapp ("B_in", [e1;Eapp("B_fct_p",[e2;e3],_)],_),_) -> *)
    (*   let x = newvar() *)
    (*   and y = newvar() *)
    (*   and z = newvar() in *)
    (*   let fx = *)
    (* 	enot(eall(y,Namespace.univ_name, *)
    (* 		  eall(z,Namespace.univ_name, *)
    (* 		       eimply( *)
    (* 			 eand(eapp("B_in",[eapp("B_pair",[x;y]);e1]), *)
    (* 			      eapp("B_in",[eapp("B_pair",[x;z]);e1])), *)
    (* 			 enot(eapp("=",[y;z])))))) in *)
    (*   let taux = etau(x,Namespace.univ_name,fx) in *)
    (*   let fy =  *)
    (* 	enot(eall(z,Namespace.univ_name, *)
    (* 		  eimply( *)
    (* 		    eand(eapp("B_in",[eapp("B_pair",[taux;y]);e1]), *)
    (* 			 eapp("B_in",[eapp("B_pair",[taux;z]);e1])), *)
    (* 		    enot(eapp("=",[y;z]))))) in *)
    (*   let tauy = etau(y,Namespace.univ_name,fy) in *)
    (*   let fz =  *)
    (* 	enot(eimply( *)
    (* 	  eand(eapp("B_in",[eapp("B_pair",[taux;tauy]);e1]), *)
    (* 	       eapp("B_in",[eapp("B_pair",[taux;z]);e1])), *)
    (* 	  enot(eapp("=",[tauy;z])))) in *)
    (*   let tauz = etau(z,Namespace.univ_name,fz) in *)
    (*   let h1 = eapp("B_in",[eapp("B_pair",[taux;tauy]);e1]) *)
    (*   and h2 = eapp("B_in",[eapp("B_pair",[taux;tauz]);e1]) *)
    (*   and h3 = enot(eapp("=",[tauy;tauz])) in *)
    (*   mknode Prop "B_notin_fct_p" [e; h1; h2; h3; e1; e2; e3 ]  *)
    (* 	[| [h1;h2;h3] |] *)
    (* Egalité ensembliste  *)
    | Eapp ("B_eq", [e1; e2],_) ->
      let meta = newmeta_B e in
      mknode_item (mknode_eq Prop e e1 e2 meta g)
    | Enot (Eapp ("B_eq", [e1; e2],_),_) -> 					       
      let x = newvar() in
      let f = enot(eequiv(eapp("B_in",[x;e1]),eapp("B_in",[x;e2]))) in
      let tau = etau(x,Namespace.univ_name,f) in
      let tau_in_e1 = eapp ("B_in", [tau; e1]) in
      let tau_in_e2 = eapp ("B_in", [tau; e2]) in
      let h1 = enot tau_in_e1 in
      let h2 = tau_in_e2 in
      let h3 = tau_in_e1 in
      let h4 = enot tau_in_e2 in
      mknode Prop "B_not_eq" [e; h1; h2; h3; h4; e1; e2]
	[| [h1;h2]; [h3;h4] |]
    (* Egalité sur les paires *)
    | Eapp ("=", [e1;
  		  Eapp("B_pair", [e3; e4], _)], _) ->
      let r_eq = Index.find_eq_lr e1 in
      let rec prem_pair r_eq =
	match r_eq with
    	  |[] -> []
    	  |Eapp("B_pair",[a;b],_)::_ when a<>e3 ->
	    let y = newvar() 
	    and z = newvar() in
	    let my = newmeta_B (eapp("mult",[e;
					     evar("0");
					     eapp("meta",[y;z])])) in
	    let mz = newmeta_B (eapp("mult",[e;
					     evar("1");
					     eapp("meta",[my;z])])) in
	    mknode_item (mknode_paireq2 Prop e e1 e3 e4 [my;mz] g)
	  |_::tl -> prem_pair tl
      in prem_pair r_eq
    | _ -> []
;;


let newnodes e g _ =
  newnodes_prop e g ;;

let make_inst  m1 term g =
  let mknode m name args branches =
    [ {
      nconc = [m];
      nrule = Ext ("B", name, args);
      nprio = (Inst m);
      ngoal = g;
      nbranches = branches;
    } ]
  in

  let substitute_list v term l=
    List.map (fun x -> Expr.substitute_2nd [(v,term)] x) l 
  in
  (* TODO : Fusionner new_meta_mult avec new_meta_mult_tau *)
  let new_meta_mult l_meta e pos v term =
    let n_l_meta = substitute_list v term l_meta in
    let rec tmp l n =
      match l with
	|[] -> []
	|a::q ->
	  if n = pos then term ::(tmp q (n+1))
	  else 
	    if n > pos then
	      let nm =
		(newmeta_B (eapp("mult",
				 [e;evar(string_of_int n);
				  eapp("meta",n_l_meta)])))
	      in
	      nm::(tmp q (n+1))
	    else a ::(tmp q (n+1))
	      
    in tmp n_l_meta 0
  in
  let new_meta_mult_tau l_meta l_tau e pos v term =
    let n_l_meta = substitute_list v term l_meta
    and n_l_tau = substitute_list v term l_tau in

    let rec tmp l n =
      match l with
	|[] -> []
	|a::q -> 
	  if n <= pos 
	  then a::(tmp q (n+1))
	  else
	    (newmeta_B (eapp("mult",
			     [e;evar(string_of_int n);
			      eapp("meta",n_l_meta);
			      eapp("tau",n_l_tau)])))
	    ::(tmp q (n+1))
    in (tmp n_l_meta 0,n_l_tau)
  in

  match m1 with
    |Eapp ("B",[m],_) ->
      (match m with  
	| Eapp ("B_in", [e1;Eapp("B_pow",[e2],_)],_) ->
	  mknode_inpow (Inst m) m e1 e2 term g

	| Eapp ("B_eq", [e1; e2],_) ->
	  mknode_eq (Inst m) m e1 e2 term g
	| Enot (Eapp ("B_in", [Eapp("B_pair",[x;z],_); 
			   Eapp ("B_comp", [e2;e3], _)],_),_) ->
	  mknode_pairnotincomp (Inst m) m x z e2 e3 term g	  
	| Enot(Eapp ("B_in", [e1; Eapp ("B_dom", [e2], _)], _),_) ->
	  mknode_notindom (Inst m) m e1 e2 term g

	| Enot (Eapp ("B_in", [e1;Eapp("B_img",[e2;e3],_)],_),_) ->
	  mknode_notinimg (Inst m) m e1 e2 e3 term g
	| Enot(Eapp ("B_in", [e1; Eapp ("B_ran", [e2], _)], _),_) ->
	  mknode_notinran (Inst m) m e1 e2 term g
	| Eapp ("B_in", [Eapp("B_pair",[x;y],_);Eapp("B_over",[e3;e4],_)],_) ->
	  mknode_pairinover (Inst m) m x y e3 e4 term g
	| Eapp (
	  "mult",
	  Eapp ("=", [e1;
  		      Eapp("B_pair", [e3; e4], _)], _)::
	    Evar (s,_):: Eapp("meta",l_meta,_)::[],_) ->
	  let pos = int_of_string s in
	  let v = List.nth l_meta pos in
	  let e = eapp("=", [e1; eapp ("B_pair", [e3;e4])]) in
	  let new_meta = new_meta_mult l_meta e pos v term in
	  mknode_paireq2 (Inst m) e e1 e3 e4 new_meta g
	| Eapp (
	  "mult",
	  Enot (Eapp ("B_in",[e1;Eapp(op,l_args,_)],_),_)::
	    Evar (s,_):: Eapp("meta",l_meta,_)::[],_) ->
	  let pos = int_of_string s in
	  let v = List.nth l_meta pos in
	  let e = enot(eapp("B_in", [e1; eapp (op, l_args)])) in
	  let new_meta = new_meta_mult l_meta e pos v term in
	  let mknode_op =
	    match op with
	      |"B_cart_prod" -> mknode_notincartprod2
	      |"B_comp" -> mknode_notincomp
	      |"B_inv" -> mknode_notininv
	      |"B_restg" -> mknode_notinrestg
	      |"B_restd" -> mknode_notinrestd
	      |"B_sustg" -> mknode_notinsustg
	      |"B_sustd" -> mknode_notinsustd
	      | _ -> 
		print_string ("operateur "^op);
		assert false
	  in
	  mknode_op (Inst m) e (e1::l_args) new_meta g
	| Eapp("mult",[Eapp ("B_in", [x ; Eapp ("B_over", [e3;e4], _)],_);
		       tau_y;tau_z],_)->
	  let e = eapp ("B_in", [x ; eapp ("B_over", [e3;e4])]) in
	  mknode_inover (Inst m) e x e3 e4 [term;tau_y;tau_z] g 
	| Eapp (
	  "mult",
	  Enot (Eapp ("B_in",[x;Eapp("B_over",[e3;e4],_)],_),_)::
	    Evar (s,_):: Eapp("meta",l_meta,_)::Eapp("tau",l_tau,_)
	  ::nil,_) ->
	  let pos = int_of_string s in
	  let v = List.nth l_meta pos in
	  let e = enot(eapp("B_in", [x; eapp ("B_over", [e3;e4])])) in
	  let (new_meta,new_tau) = new_meta_mult_tau l_meta l_tau e pos v term in
	  mknode_notinover (Inst m) e x e3 e4 (new_meta@new_tau)  g
	
	| Eapp("mult",Eapp ("B_in",[r; Eapp ("B_fct_p",[s; t] ,_)] ,_)::Evar(n,_)::Eapp("meta",l_meta,_)::[],_) ->
	  let pos = int_of_string n in 
	  let v = List.nth l_meta (pos-1) in 
	  let e = eapp ("B_in",[r; eapp ("B_fct_p",[s; t])]) in 
	  let new_meta = new_meta_mult l_meta e pos v term in 
	  (match new_meta with
	    |[m1;m2;m3;m4]->
              let h1 = eapp ("=",[m4; m3]) in 
	      let h2 = enot (eapp ("B_in",[m2; r])) in 
	      let h3 = enot (eapp ("B_in",[m2; r])) in 
	      let h4 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m4]); r])) in 
	      let h5 = enot (eapp ("B_in",[m2; r])) in 
	      let h6 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m3]); r])) in 
	      let h7 = eapp ("=",[m4; m3]) in 
	      let h8 = eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])])))])]) in 
	      let h9 = eapp ("B_in",[etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])]))); t]) in 
	      let h10 = eapp ("B_in",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); s]) in 
	      let h11 = eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])])))])]) in 
	      let h12 = eapp ("B_in",[etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])]))); t]) in 
	      let h13 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m4]); r])) in 
	      let h14 = eapp ("B_in",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); s]) in 
	      let h15 = eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])])))])]) in 
	      let h16 = enot (eapp ("B_in",[eapp ("B_pair",[m1; m3]); r])) in 
	      let h17 = eapp ("B_in",[etau (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); evar("Z")]); eapp ("B_cart",[s; t])]))); t]) in 
	      let h18 = eapp ("B_in",[etau (evar("Y"),Namespace.univ_name,eex (evar("Z"),Namespace.univ_name,eand (eapp ("=",[m2; eapp ("B_pair",[evar("Y"); evar("Z")])]),eapp ("B_in",[eapp ("B_pair",[evar("Y"); evar("Z")]); eapp ("B_cart",[s; t])])))); s]) in 
	      mknode e "fonc_part" [e;h1;h2;h3;h4;h5;h6;h7;h8;h9;h10;h11;h12;h13;h14;h15;h16;h17;h18;r;s;t;m1;m2;m3;m4] [|[h1;h2];[h3;h4];[h5;h6];[h7;h8;h9;h10];[h11;h12;h13;h14];[h15;h16;h17;h18]|]
      |_ -> assert false)   
	|_ ->Print.expr (Print.Chan stdout) m;  assert false)
    |_ -> assert false
;;
	


let to_llargs r =
  (* let axiom r = *)
  (*   match r with *)
  (*   | Ext (_, name, c :: args) -> *)
  (*      ("zenon_" ^ name, args, [c], []) *)
  (*   | _ -> assert false *)
  (* in *)
  let alpha r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1; h2] ])
    | _ -> assert false
  in
  let alpha_1 r =
    match r with
    | Ext (_, name, c :: h1 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1]])
    | _ -> assert false
  in
  let alpha_3 r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: h3 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1; h2; h3] ])
    | _ -> assert false
  in
  (* let alpha_4 r = *)
  (*   match r with *)
  (*   | Ext (_, name, c :: h1 :: h2 :: h3 :: h4 :: args) -> *)
  (*      ("zenon_" ^ name, args, [c], [ [h1; h2; h3; h4] ]) *)
  (*   | _ -> assert false *)
  (* in *)
  let beta r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1]; [h2] ])
    | _ -> assert false
  in
  let beta_2 r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: h3 :: h4 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1;h2] ; [h3;h4] ])
    | _ -> assert false
  in
  let beta_2_bis r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: h3 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1;h2] ; [h3;h2] ])
    | _ -> assert false
  in
  let beta_3 r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: h3 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1] ;[h2]; [h3] ])
    |_ -> assert false
  in
  let beta_3_bis r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: h3 :: h4 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1] ;[h2;h3];[h4;h3] ])
    |_ -> assert false
  in
  (* let beta_7 r = *)
  (*   match r with *)
  (*   | Ext (_, name, c :: h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: args) -> *)
  (*      ("zenon_" ^ name, args, [c],  *)
  (* 	[ [h0] ; [h1] ; [h2]; [h3]; [h4]; [h5]; [h6] ]) *)
  (*   | _ -> assert false *)
  (* in *)
  let alpha_2_beta r =
    match r with
      | Ext (_, name, c :: h1 :: h2 :: h3 :: args) ->
	("zenon_" ^ name, args, [c], [ [h1; h2] ; [h3] ])
    | _ -> assert false
  in
  let alpha_beta_2 r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: h3 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1] ; [h2; h3] ])
    | _ -> assert false
  in
  let alpha_3_beta_2 r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: h3 ::h4:: args) ->
       ("zenon_" ^ name, args, [c], [ [h1;h2; h3] ; [h1;h4] ])
    | _ -> assert false
  in
  (* let alpha_2_beta_2 r = *)
  (*   match r with *)
  (*   | Ext (_, name, c :: h1 :: h2 :: h3 :: args) -> *)
  (*      ("zenon_" ^ name, args, [c], [  [h1;h2];[h3;h2] ]) *)
  (*   | _ -> assert false *)
  (* in *)
  match r with
  | Ext (_, "B_in_cart_prod", _) -> alpha r
  | Ext (_, "B_notin_cart_prod", _) -> beta r
  | Ext (_, "B_in_cart_prod_2", _) -> alpha_3 r
  | Ext (_, "B_notin_cart_prod_2", _) -> beta_3 r
  | Ext (_, "B_pair_eq", _) -> alpha r
  | Ext (_, "B_pair_eq_2", _) -> alpha_beta_2 r
  | Ext (_, "B_in_cup", _) -> beta r
  | Ext (_, "B_notin_cup", _) -> alpha r
  | Ext (_, "B_in_cap", _) -> alpha r
  | Ext (_, "B_notin_cap", _) -> beta r
  | Ext (_, "B_in_diff", _) -> alpha r
  | Ext (_, "B_notin_diff", _) -> beta r
  | Ext (_, "B_in_ext", _) -> alpha_1 r
  | Ext (_, "B_notin_ext", _) -> alpha_1 r
  | Ext (_, "B_in_ext_2", _) -> beta r
  | Ext (_, "B_notin_ext_2", _) -> alpha r
  | Ext (_, "B_in_empty", _) -> alpha r
  | Ext (_, "B_in_inv", _) -> alpha r
  | Ext (_, "B_notin_inv", _) -> beta r
  | Ext (_, "B_pair_in_inv", _) -> alpha_1 r
  | Ext (_, "B_pair_notin_inv", _) -> alpha_1 r
  | Ext (_, "B_in_dom", _) -> alpha_1 r
  | Ext (_, "B_notin_dom", _) -> alpha_1 r
  | Ext (_, "B_in_ran", _) -> alpha_1 r
  | Ext (_, "B_notin_ran", _) -> alpha_1 r
  | Ext (_, "B_pair_in_comp", _) -> alpha r
  | Ext (_, "B_pair_notin_comp", _) -> beta r
  | Ext (_, "B_in_comp", _) -> alpha_3 r
  | Ext (_, "B_notin_comp", _) -> beta_3 r
  | Ext (_, "B_pair_in_id", _) -> alpha r
  | Ext (_, "B_pair_notin_id", _) -> beta r
  | Ext (_, "B_in_id", _) -> alpha(* _4 *) r
  | Ext (_, "B_notin_id", _) -> beta(* _4 *) r
  | Ext (_, "B_pair_in_restg", _) -> alpha r
  | Ext (_, "B_pair_notin_restg", _) -> beta r
  | Ext (_, "B_in_restg", _) -> alpha_3 r
  | Ext (_, "B_notin_restg", _) -> beta_3 r
  | Ext (_, "B_pair_in_restd", _) -> alpha r
  | Ext (_, "B_pair_notin_restd", _) -> beta r
  | Ext (_, "B_in_restd", _) -> alpha_3 r
  | Ext (_, "B_notin_restd", _) -> beta_3 r
  | Ext (_, "B_pair_in_sustg", _) -> alpha r
  | Ext (_, "B_pair_notin_sustg", _) -> beta r
  | Ext (_, "B_in_sustg", _) -> alpha_3 r
  | Ext (_, "B_notin_sustg", _) -> beta_3 r
  | Ext (_, "B_pair_in_sustd", _) -> alpha r
  | Ext (_, "B_pair_notin_sustd", _) -> beta r
  | Ext (_, "B_in_sustd", _) -> alpha_3 r
  | Ext (_, "B_notin_sustd", _) -> beta_3 r
  | Ext (_, "B_in_img", _) -> alpha r
  | Ext (_, "B_notin_img", _) -> beta r
  | Ext (_, "B_pair_in_over", _) -> alpha_2_beta r
  | Ext (_, "B_pair_notin_over", _) -> beta_2_bis r
  | Ext (_, "B_in_over", _) -> alpha_3_beta_2 r
  | Ext (_, "B_notin_over", _) -> beta_3_bis r
  | Ext (_, "B_in_fct_p", _) -> beta_3 r
  | Ext (_, "B_notin_fct_p", _) -> alpha_3 r
  | Ext (_, "B_in_pow", _) -> beta r	(* alpha_1 r *)
  | Ext (_, "B_notin_pow", _) -> alpha r
  | Ext (_, "B_eq", _) -> beta_2 r
  | Ext (_, "B_not_eq", _) -> beta_2 r
  | Ext (_,s,_) -> failwith s
  | _ -> assert false
;;



let to_llproof tr_expr mlp args =
  let new_node l_tau =
    let l_var = List.map
      (fun x -> 
	evar (Index.make_tau_name x)) l_tau in
    let (name, meta, con, hyps) = to_llargs mlp.mlrule in
    let tmeta = List.map tr_expr (l_var@meta) in
    let tcon = List.map tr_expr con in
    let thyps = List.map (List.map tr_expr) hyps in
    let (subs, exts) = List.split (Array.to_list args) in
    let ext = List.fold_left Expr.union [] exts in
    let extras = Expr.diff ext mlp.mlconc in
    let nn = {
      Llproof.conc = List.map tr_expr (extras @@ mlp.mlconc);
      Llproof.rule = Llproof.Rextension ("B",name, tmeta, tcon, thyps);
      Llproof.hyps = subs;
    }
    in (nn, extras)
  in
  let new_node_2 l_tau =
    let (name, meta, con, hyps) = to_llargs mlp.mlrule in
    let tmeta = List.map tr_expr (l_tau@meta) in
    let tcon = List.map tr_expr con in
    let thyps = List.map (List.map tr_expr) hyps in
    let (subs, exts) = List.split (Array.to_list args) in
    let ext = List.fold_left Expr.union [] exts in
    let extras = Expr.diff ext mlp.mlconc in
    let nn = {
      Llproof.conc = List.map tr_expr (extras @@ mlp.mlconc);
      Llproof.rule = Llproof.Rextension ("B",name, tmeta, tcon, thyps);
      Llproof.hyps = subs;
    }
    in (nn, extras)
  in
  match mlp.mlrule with
    | Ext (_, "B_notin_pow", [e; h1; h2; e1; e2]) ->
      let l_tau =
	match h1 with
    	  |Eapp("B_in",[tau;_],_) -> [tau]
	  |_ -> assert false
      in
      new_node l_tau
    | Ext (_, "B_not_eq", [e; h1; h2; h3; h4; e1; e2]) ->
      let l_tau =
	match h1 with
    	  |Enot(Eapp("B_in",[tau;_],_),_) ->[tau]
	  |_ -> assert false
      in
      new_node l_tau
    | Ext (_, "B_in_inv", [e; h1; h2; e1; e2]) ->
      let l_tau =
	match h1 with
	  |Eapp("=",[_;Eapp("B_pair",[tau1;tau2],_)],_) ->
 	    [tau1;tau2]	
	  |_ -> assert false
      in
      new_node l_tau
    | Ext (_, "B_in_dom", [e; h; e1; e2]) ->
      let l_tau =
	match h with
	  |Eapp("B_in", [Eapp ("B_pair", [_;tau],_);_],_) -> 
	    [tau]	
	  |_ -> assert false
      in
      new_node l_tau
    | Ext (_, "B_in_ran", [e; h; e1; e2]) ->
      let l_tau =
	match h with
	  |Eapp("B_in", [Eapp ("B_pair", [tau;_],_);_],_) -> 
   	    [tau]	
	  |_ -> assert false
      in
      new_node l_tau
    | Ext (_, "B_in_cart_prod_2", [e; h1; h2; h3; e1; e2; e3]) ->
      let l_tau =
	match h1 with
      	  |Eapp("=",[_;Eapp("B_pair",[tau1;tau2],_)],_)-> 
	    [tau1;tau2]	
	  |_ -> assert false
      in
      new_node l_tau
    | Ext (_, "B_in_comp", [e; h1; h2; h3; e1; e2; e3 ]) ->
      let l_tau =
	match (h1,h2) with
	  |(Eapp("=",[_;Eapp("B_pair",[x;z],_)],_),
	    Eapp("B_in",[Eapp("B_pair",[_;y],_);_],_))
	    -> [x;y;z]
	  |_ -> assert false
      in
      new_node l_tau
    | Ext (_, "B_pair_in_comp", [e; h1; h2; x; z; e2; e3 ]) ->
      (match h1 with
      	|Eapp("B_in",[Eapp("B_pair",[x;tau],_);_],_)->
	  new_node [tau]
	|_ -> assert false)
    | Ext(_,"B_in_id", [e; h1; h2; e1; e2 ]) ->
      (match h1 with
    	|Eapp("=",[_;Eapp("B_pair",[tau;_],_)],_) ->
    	  new_node [tau]
    	|_ -> assert false)
    (* | Ext(_,"B_in_id", [e; h1; h2; h3; h4; e1; e2 ]) -> *)
    (*   (match h1 with *)
    (* 	|Eapp("=",[_;Eapp("B_pair",[tau1;tau2],_)],_) -> *)
    (* 	  new_node [tau1;tau2] *)
    (* 	|_ -> assert false) *)
    | Ext(_,"B_in_restg", [e; h1; h2; h3; e1; e2;e3 ]) ->
      (match h1 with
      	|Eapp("=",[_;Eapp("B_pair",[taux;tauy],_)],_)->
	  new_node [taux;tauy]
	|_ -> assert false)
    | Ext(_,"B_in_restd", [e; h1; h2; h3; e1; e2;e3 ]) ->
      (match h1 with
      	|Eapp("=",[_;Eapp("B_pair",[taux;tauy],_)],_)->
	  new_node [taux;tauy]
	|_ -> assert false)
    | Ext(_,"B_in_sustg", [e; h1; h2; h3; e1; e2;e3 ]) ->
      (match h1 with
      	|Eapp("=",[_;Eapp("B_pair",[taux;tauy],_)],_)->
	  new_node [taux;tauy]
	|_ -> assert false)
    | Ext(_,"B_in_sustd", [e; h1; h2; h3; e1; e2;e3 ]) ->
      (match h1 with
      	|Eapp("=",[_;Eapp("B_pair",[taux;tauy],_)],_)->
	  new_node [taux;tauy]
	|_ -> assert false)
    | Ext(_,"B_in_img", [e; h1; h2; e1; e2; e3 ]) ->
      (match h1 with 
      	|Eapp("B_in",[tau;_],_)->
	  new_node [tau]
	|_ -> assert false)
    | Ext(_,"B_pair_notin_over", [e; h1; h2;h3; x; y; e3; e4 ]) ->
       (match h3 with
    	|Eapp("B_in",[Eapp("B_pair",[_;tau],_);_],_)->
    	  new_node_2 [tau]
     	|_ -> assert false)
    | Ext(_,"B_in_over", [e; h1; h2; h3; h4; x; e3; e4;meta ]) ->
       (match h1 with
    	|Eapp("=",[_;Eapp("B_pair",[taux;tauy],_)],_)->
    	  new_node_2 [taux;tauy]
     	|_ -> assert false)
    | Ext(_,"B_notin_over", [e; h1; h2; h3; h4; x; e3; e4;meta1;meta2 ]) ->
      (match h4 with
    	|Eapp("B_in",[Eapp("B_pair",[_;tau],_);_],_)->
    	  new_node_2 [tau]
     	|_ -> assert false)
	    
    | Ext(_,"B_notin_fct_p", [e; h1; h2; h3; e1; e2; e3 ]) ->
      (match h1,h2 with 
      	|(Eapp("B_in",[Eapp("B_pair",[taux;tauy],_);_],_),
	  Eapp("B_in",[Eapp("B_pair",[_;tauz],_);_],_)) ->
	  new_node [taux;tauy;tauz]
	|_ -> assert false)
    | _ -> 
      let (name, meta, con, hyps) = to_llargs mlp.mlrule in
      let tmeta = List.map tr_expr meta in
      let tcon = List.map tr_expr con in
      let thyps = List.map (List.map tr_expr) hyps in
      let (subs, exts) = List.split (Array.to_list args) in
      let ext = List.fold_left Expr.union [] exts in
      let extras = Expr.diff ext mlp.mlconc in
      let nn = {
        Llproof.conc = List.map tr_expr (extras @@ mlp.mlconc);
        Llproof.rule = Llproof.Rextension ("B",name, tmeta, tcon, thyps);
        Llproof.hyps = subs;
      }
      in (nn, extras)
;;


let preprocess l = l;;

let add_phrase p = ();;

let postprocess p = p;;

let declare_context_coq oc =
  fprintf oc "Require Import zenon_b.\n";
;;

let p_rule_coq oc r =
  let poc fmt = fprintf oc fmt in
  match r with
  | Llproof.Rextension ("B","zenon_B_notin_pow", tau::args, conc, hyps) ->
    begin
    poc "apply (%s_s%a%a)" "zenon_B_notin_pow" p_expr_list args p_name_list conc;
    let hd =
      (match tau with
    	| Evar (n, _) -> n
    	| _ -> assert false) in
    poc "; [ zenon_intro %s ;" hd ;
    poc " %a ].\n" (p_list "" p_intros " | ") hyps
      end
  | Llproof.Rextension ("B","zenon_B_not_eq", tau::args, conc, hyps) ->
    begin
      let s_tau =
  	(match tau with
  	  | Evar (n, _) -> n
  	  | _ -> assert false) in
      
      poc "apply (%s_s%a%a)" "zenon_B_not_eq" p_expr_list args p_name_list conc;
      let zenon_intro_1 = " zenon_intro "^s_tau^" ;" in
      poc "; [ zenon_intro %s ;" s_tau ;
      poc " %a ].\n" (p_list "" p_intros (" | "^zenon_intro_1)) hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_dom", tau::args, conc, hyps) ->
    begin
      let s_tau =
  	(match tau with
  	  | Evar (n, _) -> n
  	  | _ -> assert false) in
      
      poc "apply (%s_s%a%a)" "zenon_B_in_dom" p_expr_list args p_name_list conc;
      poc "; [ zenon_intro %s ;" s_tau ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_ran", tau::args, conc, h) ->
    begin
      let hd =
  	(match tau with
  	  | Evar (n, _) -> n
  	  | _ -> assert false) in
      poc "apply (%s_s%a%a)" "zenon_B_in_ran" p_expr_list args p_name_list conc;
      poc "; [ zenon_intro %s ;" hd ;
      poc " %a ].\n" (p_list "" p_intros " | ") h
    end
  | Llproof.Rextension ("B","zenon_B_pair_in", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_pair_in" p_expr_list args p_name_list conc;
      let (hd,hd2) =
	(match tau1,tau2 with
    	  | Evar (n, _),Evar(n2,_) -> n,n2
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" hd ;
      poc " zenon_intro %s ;" hd2 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_inv", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_inv" p_expr_list args p_name_list conc;
      let (hd,hd2) =
	(match tau1,tau2 with
    	  | Evar (n, _),Evar(n2,_) -> n,n2
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" hd ;
      poc " zenon_intro %s ;" hd2 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_cart_prod_2", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_cart_prod_2" p_expr_list args p_name_list conc;
      let (hd,hd2) =
	(match tau1,tau2 with
    	  | Evar (n, _),Evar(n2,_) -> n,n2
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" hd ;
      poc " zenon_intro %s ;" hd2 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_pair_in_comp", tau::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_pair_in_comp" p_expr_list args p_name_list conc;
      let hd =
	(match tau with
    	  | Evar (n, _) -> n
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" hd ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_comp", tau1::tau2::tau3::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_comp" p_expr_list args p_name_list conc;
      let t1,t2,t3 =
	(match tau1,tau2,tau3 with
    	  | Evar (n1, _),Evar (n2, _),Evar (n3, _) -> n1,n2,n3
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" t1 ;
      poc " zenon_intro %s ;" t2 ;
      poc " zenon_intro %s ;" t3 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_id", tau::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_id" p_expr_list args p_name_list conc;
      let t1 =
  	(match tau with
    	  | Evar (n1, _) -> n1
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" t1 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  (* | Llproof.Rextension ("B","zenon_B_in_id", tau::tau2::args, conc, hyps) -> *)
  (*   begin *)
  (*     poc "apply (%s_s%a%a)" "zenon_B_in_id" p_expr_list args p_name_list conc; *)
  (*     let t1,t2 = *)
  (* 	(match tau,tau2 with *)
  (*   	  | Evar (n1, _),Evar(n2,_) -> n1,n2 *)
  (*   	  | _ -> assert false) in *)
  (*     poc "; [ zenon_intro %s ;" t1 ; *)
  (*     poc " zenon_intro %s ;" t2 ; *)
  (*     poc " %a ].\n" (p_list "" p_intros " | ") hyps *)
  (*   end *)
  | Llproof.Rextension ("B","zenon_B_in_restg", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_restg" p_expr_list args p_name_list conc;
      let t1,t2 =
	(match tau1,tau2 with
    	  | Evar (n1, _),Evar (n2, _) -> n1,n2
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" t1 ;
      poc " zenon_intro %s ;" t2 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_restd", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_restd" p_expr_list args p_name_list conc;
      let t1,t2 =
	(match tau1,tau2 with
    	  | Evar (n1, _),Evar (n2, _) -> n1,n2
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" t1 ;
      poc " zenon_intro %s ;" t2 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_sustg", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_sustg" p_expr_list args p_name_list conc;
      let t1,t2 =
	(match tau1,tau2 with
    	  | Evar (n1, _),Evar (n2, _) -> n1,n2
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" t1 ;
      poc " zenon_intro %s ;" t2 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_sustd", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_sustd" p_expr_list args p_name_list conc;
      let t1,t2 =
	(match tau1,tau2 with
    	  | Evar (n1, _),Evar (n2, _) -> n1,n2
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" t1 ;
      poc " zenon_intro %s ;" t2 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_img", tau1::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_img" p_expr_list args p_name_list conc;
      let t1 =
	(match tau1 with
    	  | Evar (n1, _) -> n1
    	  | _ -> assert false) in
      poc "; [  zenon_intro %s ;" t1 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B","zenon_B_pair_notin_over", tau1::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_pair_notin_over" p_expr_list args p_name_list conc;

       let t1 = Index.make_tau_name tau1 in
      let zenon_intro_1 = " zenon_intro "^t1^" ;"
      in
      poc ";[%a ].\n" (p_list "" p_intros (" | "^zenon_intro_1)) hyps
    end
  | Llproof.Rextension ("B","zenon_B_notin_over", tau1::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_notin_over" p_expr_list args p_name_list conc; 
      let t1 = Index.make_tau_name tau1 in
      let zenon_intro_1 = " zenon_intro "^t1^" ;"
      in
      poc ";[%a ].\n" (p_list "" p_intros (" | "^zenon_intro_1)) hyps
    end
  | Llproof.Rextension ("B","zenon_B_in_over", tau1::tau2::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_in_over" p_expr_list args p_name_list conc;
       let t1,t2 = Index.make_tau_name tau1,Index.make_tau_name tau2 in
       poc "; [ zenon_intro %s ;" t1 ;
       poc " zenon_intro %s ;" t2 ;
      let zenon_intro_1 = " zenon_intro "^t1^" ;" 
      and zenon_intro_2 = " zenon_intro "^t2^" ;" 
      in
      poc "%a ].\n" (p_list "" p_intros (" | "^zenon_intro_1^zenon_intro_2)) hyps
    end
  | Llproof.Rextension ("B","zenon_B_notin_fct_p", tau1::tau2::tau3::args, conc, hyps) ->
    begin
      poc "apply (%s_s%a%a)" "zenon_B_notin_fct_p" p_expr_list args p_name_list conc;
      let t1,t2,t3 =
	(match tau1,tau2,tau3 with
    	  | Evar (n1, _),Evar (n2, _),Evar (n3, _) -> n1,n2,n3
    	  | _ -> assert false) in
      poc "; [ zenon_intro %s ;" t1 ;
      poc " zenon_intro %s ;" t2 ;
      poc " zenon_intro %s ;" t3 ;
      poc " %a ].\n" (p_list "" p_intros " | ") hyps
    end
  | Llproof.Rextension ("B", name, args, conc, hyps) ->
    poc "apply (%s_s%a%a)" name p_expr_list args p_name_list conc;
    begin match hyps with
      | [] -> poc ".\n";
      | _ -> poc "; [ %a ].\n" (p_list "" p_intros " | ") hyps;
    end;
    
  | Llproof.Rextension (a,b,_,_,_) -> 
    Printf.printf ("%s %s") a b;
    assert false
  | _ -> assert false
;;


let predef () = b_expr @ b_pred ;;

Extension.register {
  Extension.name = "B";
  Extension.newnodes = newnodes;
  Extension.make_inst = make_inst;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = preprocess;
  Extension.add_phrase = add_phrase;
  Extension.postprocess = postprocess;
  Extension.to_llproof = to_llproof;
  Extension.p_rule_coq = p_rule_coq;
  Extension.declare_context_coq = declare_context_coq;
  Extension.predef = predef;
};;
