open Sat_solver_lib

let test_has_empty_clause_true () =
  let f = [ [1; -2]; [] ] in
  assert (Cnf.has_empty_clause f = true)

let test_has_empty_clause_false () =
  let f = [ [1; -2]; [2; 3] ] in
  assert (Cnf.has_empty_clause f = false)

let test_has_empty_clause_on_empty_formula () =
  assert (Cnf.has_empty_clause [] = false)

let () =
  test_has_empty_clause_true ();
  test_has_empty_clause_false ();
  test_has_empty_clause_on_empty_formula ();
  print_endline "all tests passed"