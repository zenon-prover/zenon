(*  Copyright 2008 INRIA  *)
Version.add "$Id$";;

open Printf;;

let number = 266;;      (* strictly increasing *)
let date = "2016-07-05";;

let major = 0;;
let minor = 8;;
let bugfix = 2;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
