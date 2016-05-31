(*  Copyright 2008 INRIA  *)
Version.add "$Id$";;

open Printf;;

let number = 264;;      (* strictly increasing *)
let date = "2016-05-31";;

let major = 0;;
let minor = 8;;
let bugfix = 1;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
