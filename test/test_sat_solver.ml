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

let test_variable_outside_declared_range =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"variables beyond n are dead literals for both solvers"
    (fun () ->
      Dpll.solve 0 [ [ -1] ] = Dpll.Unsat
      && Bruteforce.solve 0 [ [ -1] ] = Bruteforce.Unsat
      && Dpll.solve 1 [ [2] ] = Dpll.Unsat
      && Bruteforce.solve 1 [ [2] ] = Bruteforce.Unsat
      && Dpll.solve 1 [ [2; 1] ] = Dpll.Sat [ 1 ]
      && Bruteforce.solve 1 [ [2; 1] ] <> Bruteforce.Unsat)

let test_zero_literal_is_unsatisfiable =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"literal 0 makes a clause unsatisfiable"
    (fun () ->
      Dpll.solve 2 [ [0] ] = Dpll.Unsat
      && Bruteforce.solve 2 [ [0] ] = Bruteforce.Unsat)

let prop_propagation_no_duplicate_vars =
  QCheck.Test.make ~name:"unit_propagate assigns each variable once"
    QCheck.(list (list (int_range (-5) 5)))
    (fun f ->
      let f = List.filter (fun c -> not (List.mem 0 c)) f in
      let (assign, _) = Dpll.unit_propagate [] f in
      let vars = List.map abs assign in
      List.length vars = List.length (List.sort_uniq compare vars))

let prop_dpll_matches_brute_force =
  QCheck.Test.make ~name:"DPLL agrees with brute force on small formulas"
    QCheck.(pair (int_range 1 5) (list (list (int_range (-5) 5))))
    (fun (n, raw_clauses) ->
      let f = List.filter (fun c -> not (List.mem 0 c)) raw_clauses in
      let bf_sat = (Bruteforce.solve n f) <> Bruteforce.Unsat in
      let dpll_sat = (Dpll.solve n f) <> Dpll.Unsat in
      bf_sat = dpll_sat)

let () =
  QCheck_runner.run_tests_main
    [ prop_empty_clause_detected;
      prop_num_clauses_matches_length;
      test_dimacs_parse;
      test_brute_force_unsat;
      test_variable_outside_declared_range;
      test_zero_literal_is_unsatisfiable;
      prop_propagation_no_duplicate_vars;
      prop_dpll_matches_brute_force ]
