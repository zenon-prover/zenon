(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.89 2012-05-09 13:46:29 doligez Exp $";;

open Printf;;

let number = 251;;      (* strictly increasing *)
let date = "2012-05-09";;

let major = 0;;
let minor = 7;;
let bugfix = 1;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
