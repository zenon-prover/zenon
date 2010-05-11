(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.80 2010-05-11 15:53:20 doligez Exp $";;

open Printf;;

let number = 230;;      (* strictly increasing *)
let date = "2010-05-11";;

let major = 0;;
let minor = 7;;
let bugfix = 0;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
