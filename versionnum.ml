(*  Copyright 2008 INRIA  *)

open Printf;;

let number = 269;;      (* strictly increasing *)
let date = "2018-09-18";;

let major = 0;;
let minor = 8;;
let bugfix = 4;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
