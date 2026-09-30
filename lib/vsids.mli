type t

val create : int -> t
val bump : t -> int -> unit
val decay_all : t -> unit
val best_unassigned : t -> (int -> bool) -> int option