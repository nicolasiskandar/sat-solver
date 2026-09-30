type result = Sat of int list | Unsat

let rec all_assignments (n : int) : int list list =
  if n = 0 then [ [] ]
  else
    let rest = all_assignments (n - 1) in
    List.concat_map (fun a -> [ n :: a; (-n) :: a ]) rest

let solve (n : int) (f : Cnf.formula) : result =
  let candidates = all_assignments n in
  match List.find_opt (fun a -> Cnf.satisfies a f) candidates with
  | Some a -> Sat a
  | None -> Unsat