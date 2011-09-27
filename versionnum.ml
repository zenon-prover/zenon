(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.84 2011-09-27 14:29:17 doligez Exp $";;

open Printf;;

let number = 238;;      (* strictly increasing *)
let date = "2011-04-26";;

let major = 0;;
let minor = 7;;
let bugfix = 0;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
