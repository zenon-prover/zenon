(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.83 2010-07-01 16:17:29 doligez Exp $";;

open Printf;;

let number = 233;;      (* strictly increasing *)
let date = "2010-07-01";;

let major = 0;;
let minor = 7;;
let bugfix = 0;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
