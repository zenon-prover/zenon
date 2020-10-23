(*  Copyright 2008 INRIA  *)

open Printf;;

let number = 270;;      (* strictly increasing *)
let date = "2020-10-23";;

let major = 0;;
let minor = 8;;
let bugfix = 5;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
