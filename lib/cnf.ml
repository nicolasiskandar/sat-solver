type literal = int
type clause = literal list
type formula = clause list

let is_empty_clause (c : clause) : bool = c = []

let has_empty_clause (f : formula) : bool =
  List.exists is_empty_clause f

let num_clauses (f : formula) : int = List.length f

let clause_satisfied (assign : int list) (clause : clause) : bool =
  List.exists (fun lit -> List.mem lit assign) clause

let satisfies (assign : int list) (f : formula) : bool =
  List.for_all (clause_satisfied assign) f
