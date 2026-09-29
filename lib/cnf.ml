type literal = int
type clause = literal list
type formula = clause list

let is_empty_clause (c : clause) : bool = c = []

let has_empty_clause (f : formula) : bool =
  List.exists is_empty_clause f

let num_clauses (f : formula) : int = List.length f
