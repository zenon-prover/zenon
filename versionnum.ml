(*  Copyright 2008 INRIA  *)
Version.add "$Id: ab585d9a410f688ff4dca562e70d1f2f67af9723 $";;

open Printf;;

let number = 262;;      (* strictly increasing *)
let date = "2014-09-19";;

let major = 0;;
let minor = 7;;
let bugfix = 2;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
