type result = Sat of int list | Unsat

val solve : int -> Cnf.formula -> result
