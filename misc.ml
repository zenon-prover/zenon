(*  Copyright 2003 INRIA  *)
Version.add "$Id: misc.ml,v 1.2 2004-04-29 13:04:52 doligez Exp $";;


(* functions missing from the standard library *)

let rec index n e = function
  | [] -> raise Not_found
  | h :: _ when h = e -> n
  | _ :: t -> index (n+1) e t
;;
