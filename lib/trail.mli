type reason = Decision | Propagated of Cnf.clause

type entry = { lit : int; level : int; pos : int; reason : reason }

type t

val create : int -> t
val current_level : t -> int
val push_decision : t -> int -> unit

val push_propagated : t -> int -> Cnf.clause -> unit

val entries : t -> entry list

val entry_of : t -> int -> entry option

val value : t -> int -> bool option

val undo_to_level : t -> int -> unit
