(*  Copyright 2004 INRIA  *)
(*  $Id: version.ml,v 1.21 2005-11-09 15:18:24 doligez Exp $  *)

let number = 27;;      (* strictly increasing *)
let date = "2005-11-08";;

let major = 0;;
let minor = 4;;
let bugfix = 0;;       (* even = development version; odd = released version *)

let short = Printf.sprintf "%d.%d.%d" major minor bugfix;;

let full =
  Printf.sprintf "%d.%d.%d [%d] %s" major minor bugfix number date
;;


(* CVS version strings *)

let version_list =
   ref ["$Id: version.ml,v 1.21 2005-11-09 15:18:24 doligez Exp $"]
;;

let add x = (version_list := x :: !version_list);;

let print_cvs ch =
  List.iter (fun x -> Printf.fprintf ch "%s\n" x) !version_list
;;
