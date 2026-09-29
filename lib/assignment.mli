type value = True | False | Unassigned

type t

val create : int -> t

val value_of : t -> int -> value

val set : t -> int -> bool -> unit

val unset : t -> int -> unit

val is_fully_assigned : t -> bool