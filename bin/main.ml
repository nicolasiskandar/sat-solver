open Sat_solver_lib

let unsat_formula n =
  List.concat_map
    (fun i -> [ [i; i+1]; [-i; -(i+1)]; [i; -(i+1)]; [-i; i+1] ])
    (List.init (n/2) (fun k -> 2*k + 1))

let () =
  List.iter
    (fun n ->
      let f = unsat_formula n in
      let start = Sys.time () in
      let result = Bruteforce.solve n f in
      let elapsed = Sys.time () -. start in
      Printf.printf "n=%2d  result=%s  time=%.4fs\n"
        n
        (match result with Bruteforce.Sat _ -> "SAT" | Unsat -> "UNSAT")
        elapsed)
    [ 4; 8; 12; 16; 20; 24 ]