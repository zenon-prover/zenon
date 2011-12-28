(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.85 2011-12-28 16:43:33 doligez Exp $";;

open Printf;;

let number = 239;;      (* strictly increasing *)
let date = "2011-12-27";;

let major = 0;;
let minor = 7;;
let bugfix = 0;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
