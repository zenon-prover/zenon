(*  Copyright 2004 INRIA  *)
(* Version.add "$Id: version.ml,v 1.1 2004-04-29 13:04:52 doligez Exp $";; *)

let major = 0;;
let minor = 1;;
let bugfix = 2;;
let date = "2004-04-29";;

let number = 0;;

let short = Printf.sprintf "%d.%d.%d" major minor bugfix;;

let full =
  Printf.sprintf "%d.%d.%d [%d] %s" major minor bugfix number date
;;


(* CVS version strings *)

let version_list =
   ref ["$Id: version.ml,v 1.1 2004-04-29 13:04:52 doligez Exp $"]
;;

let add x = (version_list := x :: !version_list);;

let print_cvs ch =
  List.iter (fun x -> Printf.fprintf ch "%s\n" x) !version_list
;;
