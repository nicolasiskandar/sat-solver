open Sat_solver_lib

let prop_empty_clause_detected = 
  QCheck.Test.make ~name:"formula with [] clause is detected"
    QCheck.(list (list small_int))
    (fun other_clauses ->
      let f = [] :: other_clauses in
      Cnf.has_empty_clause f = true)

let prop_num_clauses_matches_length =
  QCheck.Test.make ~name:"num_clauses matches List.length"
    QCheck.(list (list small_int))
    (fun f -> Cnf.num_clauses f = List.length f)