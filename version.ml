(*  Copyright 2004 INRIA  *)
(* Version.add "$Id: version.ml,v 1.2 2004-05-26 16:23:52 doligez Exp $";; *)

let major = 0;;
let minor = 2;;
let bugfix = 0;;

let date = "2004-05-25";;
let number = 1;;  (* Ce nombre ne doit JAMAIS decroitre. *)

let short = Printf.sprintf "%d.%d.%d" major minor bugfix;;

let full =
  Printf.sprintf "%d.%d.%d [%d] %s" major minor bugfix number date
;;


(* CVS version strings *)

let version_list =
   ref ["$Id: version.ml,v 1.2 2004-05-26 16:23:52 doligez Exp $"]
;;

let add x = (version_list := x :: !version_list);;

let print_cvs ch =
  List.iter (fun x -> Printf.fprintf ch "%s\n" x) !version_list
;;
