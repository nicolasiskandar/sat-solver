open Sat_solver_lib

let unsat_formula n =
  List.concat_map
    (fun i -> [ [i; i+1]; [-i; -(i+1)]; [i; -(i+1)]; [-i; i+1] ])
    (List.init (n/2) (fun k -> 2*k + 1))

let sat_formula n =
  List.concat_map
    (fun k ->
      let i = 2 * k + 1 in
      if k mod 2 = 0 then [ [i; i+1]; [-i; -(i+1)]; [i; -(i+1)] ]
      else [ [i; i+1]; [-i; -(i+1)]; [-i; i+1] ])
    (List.init (n/2) (fun k -> k))

let () =
  List.iter
    (fun n ->
      let f = unsat_formula n in
      let start = Sys.time () in
      let result = Cdcl.solve n f in
      let elapsed = Sys.time () -. start in
      Printf.printf "n=%2d  result=%s  time=%.4fs\n"
        n
        (match result with Cdcl.Sat _ -> "SAT" | Cdcl.Unsat -> "UNSAT")
        elapsed)
    [ 4; 8; 12; 16; 20; 24 ];
  let n = 12 in
  let f = sat_formula n in
  let start = Sys.time () in
  match Cdcl.solve n f with
  | Cdcl.Sat model ->
    Printf.printf "\nn=%2d  result=SAT  time=%.4fs\nmodel=%s\nverified=%b\n"
      n (Sys.time () -. start)
      (String.concat " " (List.map string_of_int model))
      (Cnf.satisfies model f)
  | Cdcl.Unsat -> Printf.printf "\nn=%2d  result=UNSAT  time=%.4fs\n" n (Sys.time () -. start)