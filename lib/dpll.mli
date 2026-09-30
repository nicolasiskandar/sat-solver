val in_range : int -> int -> bool

val restrict : int -> Cnf.formula -> Cnf.formula

val simplify : int list -> Cnf.formula -> Cnf.formula

val find_unit_clause : Cnf.formula -> int option

val unit_propagate : int list -> Cnf.formula -> int list * Cnf.formula

val find_pure_literal : Cnf.formula -> int option

type result = Sat of int list | Unsat

val solve : int -> Cnf.formula -> result
