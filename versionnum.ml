(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.73 2010-03-31 15:32:51 doligez Exp $";;

open Printf;;

let number = 217;;      (* strictly increasing *)
let date = "2010-03-31";;

let major = 0;;
let minor = 6;;
let bugfix = 4;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
