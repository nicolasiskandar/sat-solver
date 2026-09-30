type t

val create : int -> unit -> t

val add : t -> Cnf.clause -> int option

val watched_by : t -> int -> int list

val watched : t -> int -> int * int

val lits : t -> int -> int array

val move_watch : t -> int -> from_:int -> to_:int -> unit

val to_clause : t -> int -> Cnf.clause

val num_clauses : t -> int
