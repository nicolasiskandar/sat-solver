type literal = int

type clause = literal list

type formula = clause list

val is_empty_clause : clause -> bool

val has_empty_clause : formula -> bool

val num_clauses : formula -> int

val clause_satisfied : int list -> clause -> bool

val satisfies : int list -> formula -> bool