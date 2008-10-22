(*  Copyright 2004 INRIA  *)
let myvers = "$Id: version.ml,v 1.66 2008-10-22 11:51:04 doligez Exp $";;

open Printf;;

let version_list = ref [myvers];;

let add x = (version_list := x :: !version_list);;

let print_cvs ch = List.iter (fun x -> fprintf ch "%s\n" x) !version_list;;
