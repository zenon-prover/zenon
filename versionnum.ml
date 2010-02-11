(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.70 2010-02-11 16:47:40 doligez Exp $";;

open Printf;;

let number = 214;;      (* strictly increasing *)
let date = "2010-02-11";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
