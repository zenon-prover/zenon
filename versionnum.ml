(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.67 2010-01-19 15:43:08 doligez Exp $";;

open Printf;;

let number = 210;;      (* strictly increasing *)
let date = "2010-01-19";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
