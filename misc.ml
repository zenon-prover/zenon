(*  Copyright 2003 INRIA  *)
(*  $Id: misc.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $  *)


(* version numbers *)

let version_list =
   ref ["$Id: misc.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $"]
;;

let version x = (version_list := x :: !version_list);;

let print_versions () = List.iter print_endline !version_list;;


(* functions missing from the standard library *)

let rec index n e = function
  | [] -> raise Not_found
  | h :: _ when h = e -> n
  | _ :: t -> index (n+1) e t
;;
