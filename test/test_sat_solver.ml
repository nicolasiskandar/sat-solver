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

let prop_cdcl_matches_brute_force =
  QCheck.Test.make ~name:"CDCL agrees with brute force on small formulas"
    QCheck.(pair (int_range 1 5) (list (list (int_range (-5) 5))))
    (fun (n, raw_clauses) ->
      let f = List.filter (fun c -> not (List.mem 0 c)) raw_clauses in
      let bf_sat = (Bruteforce.solve n f) <> Bruteforce.Unsat in
      let cdcl_sat = (Cdcl.solve n f) <> Cdcl.Unsat in
      bf_sat = cdcl_sat)

let test_cdcl_conflict_at_level_zero =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"CDCL reports a conflict at level 0 as Unsat"
    (fun () ->
      Cdcl.solve 1 [ [1]; [ -1] ] = Cdcl.Unsat
      && Dpll.solve 1 [ [1]; [ -1] ] = Dpll.Unsat
      && Cdcl.solve 1 [ [1; 2]; [ -1] ] = Cdcl.Unsat)

let test_cdcl_degenerate_formulas =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"CDCL handles out-of-range and empty clauses like DPLL"
    (fun () ->
      Cdcl.solve 0 [ [ -1] ] = Cdcl.Unsat
      && Cdcl.solve 2 [ []; [1] ] = Cdcl.Unsat
      && Cdcl.solve 2 [] = Cdcl.Sat [ 1; 2 ]
      && Cdcl.solve 2 [ [0] ] = Cdcl.Unsat)

let test_cdcl_pigeonhole =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"CDCL proves 3 pigeons into 2 holes unsatisfiable"
    (fun () ->
      let f =
        [ [1; 2]; [3; 4]; [5; 6];
          [ -1; -3]; [ -1; -5]; [ -2; -4];
          [ -2; -6]; [ -3; -5]; [ -4; -6] ]
      in
      Cdcl.solve 6 f = Cdcl.Unsat
      && Dpll.solve 6 f = Dpll.Unsat)

let prop_cdcl_model_is_a_model =
  QCheck.Test.make ~name:"CDCL's model satisfies every clause"
    QCheck.(pair (int_range 1 4) (list (list (int_range (-4) 4))))
    (fun (n, raw_clauses) ->
      let f = List.filter (fun c -> not (List.mem 0 c)) raw_clauses in
      match Cdcl.solve n f with
      | Cdcl.Unsat -> true
      | Cdcl.Sat model -> Cnf.satisfies model f)

let test_trail_undo_clears_assignment =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"Trail.undo_to_level clears undone assignments"
    (fun () ->
      let t = Trail.create 2 in
      Trail.push_decision t 1;
      Trail.push_propagated t 2 [ -1 ];
      let before = Trail.value t 2 = Some true && Trail.value t 1 = Some true in
      Trail.undo_to_level t 0;
      before
      && Trail.current_level t = 0
      && Trail.entries t = []
      && Trail.entry_of t 1 = None
      && Trail.value t 1 = None
      && Trail.value t 2 = None)

let test_conflict_analysis_learns_asserting_clause =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"Conflict_analysis resolves down to the UIP without negating it"
    (fun () ->
      let t = Trail.create 3 in
      Trail.push_decision t 1;
      Trail.push_propagated t 2 [ -1 ];
      Trail.push_propagated t 3 [ -2 ];
      Conflict_analysis.analyze t [ -3; -1 ] = ([ -1 ], 0))

let test_watch_list_moves_watches =
  QCheck.Test.make ~count:1 QCheck.unit
    ~name:"Watch_list indexes and moves watches"
    (fun () ->
      let w = Watch_list.create 3 () in
      let id = Option.get (Watch_list.add w [ 1; 2; 3 ]) in
      let before = Watch_list.watched w id = (1, 2) in
      let registered =
        List.mem id (Watch_list.watched_by w 1) && List.mem id (Watch_list.watched_by w 2)
      in
      Watch_list.move_watch w id ~from_:1 ~to_:3;
      before && registered
      && Watch_list.watched w id = (3, 2)
      && not (List.mem id (Watch_list.watched_by w 1))
      && List.mem id (Watch_list.watched_by w 3)
      && List.mem id (Watch_list.watched_by w 2)
      && Watch_list.to_clause w id = [ 1; 2; 3 ]
      && Watch_list.num_clauses w = 1)

let () =
  QCheck_runner.run_tests_main
    [ prop_empty_clause_detected;
      prop_num_clauses_matches_length;
      test_dimacs_parse;
      test_brute_force_unsat;
      test_variable_outside_declared_range;
      test_zero_literal_is_unsatisfiable;
      prop_propagation_no_duplicate_vars;
      prop_dpll_matches_brute_force;
      prop_cdcl_matches_brute_force;
      test_cdcl_conflict_at_level_zero;
      test_cdcl_degenerate_formulas;
      test_cdcl_pigeonhole;
      prop_cdcl_model_is_a_model;
      test_trail_undo_clears_assignment;
      test_conflict_analysis_learns_asserting_clause;
      test_watch_list_moves_watches ]
