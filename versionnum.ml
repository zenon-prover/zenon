(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.81 2010-06-04 15:37:26 doligez Exp $";;

open Printf;;

let number = 231;;      (* strictly increasing *)
let date = "2010-06-04";;

let major = 0;;
let minor = 7;;
let bugfix = 0;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
