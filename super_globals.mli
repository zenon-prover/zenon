(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
(*  $Id$  *)

val time_limit_super : unit -> float
val time_limit_init : float ref
val progress_period : int ref
val progress_counter : int ref
val progress_last : float ref
val period_base : float
