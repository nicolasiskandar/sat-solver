open Sat_solver_lib

let prop_empty_clause_detected = 
  QCheck.Test.make ~name:"formula with [] clause is detected"
    QCheck.(list (list nat_small))
    (fun other_clauses ->
      let f = [] :: other_clauses in
      Cnf.has_empty_clause f = true)

let prop_num_clauses_matches_length =
  QCheck.Test.make ~name:"num_clauses matches List.length"
    QCheck.(list (list nat_small))
    (fun f -> Cnf.num_clauses f = List.length f)

let test_dimacs_parse =
  QCheck.Test.make ~count:1 QCheck.unit ~name:"dimacs parses small.cnf"
    (fun () ->
      let (n, f) = Dimacs.parse_file "fixtures/small.cnf" in
      n = 3 && f = [ [1; -2; 3]; [-1; 2]; [3] ])

let test_brute_force_unsat =
  QCheck.Test.make ~count:1 QCheck.unit ~name:"bruteforce reports Unsat"
    (fun () ->
      let f = [ [1;2]; [-1;-2]; [1;-2]; [-1;2] ] in
      Bruteforce.solve 2 f = Unsat)

let () =
  QCheck_runner.run_tests_main
    [ prop_empty_clause_detected;
      prop_num_clauses_matches_length;
      test_dimacs_parse;
      test_brute_force_unsat ]
