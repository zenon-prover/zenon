(*  Copyright 2004 INRIA  *)
let myvers = "$Id: 34c58a3afac083cc607b116f4d95546502fbd4b7 $";;

open Printf;;

let version_list = ref [myvers];;

let add x = (version_list := x :: !version_list);;

let print_cvs ch = List.iter (fun x -> fprintf ch "%s\n" x) !version_list;;
