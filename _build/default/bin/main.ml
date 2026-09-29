let () =
  let f = [ [1; -2]; [2; 3] ] in
  if Sat_solver_lib.Cnf.has_empty_clause f then
    print_endline "formula trivially unsat"
  else
    print_endline "formula has no empty clause";
  Printf.printf "%d\n" (Sat_solver_lib.Cnf.num_clauses f)
