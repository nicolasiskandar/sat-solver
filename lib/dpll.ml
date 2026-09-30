let in_range (n : int) (lit : int) : bool =
  let v = abs lit in
  v >= 1 && v <= n

let restrict (n : int) (f : Cnf.formula) : Cnf.formula =
  List.map (fun clause -> List.filter (in_range n) clause) f

let simplify (assign : int list) (f : Cnf.formula) : Cnf.formula =
  f
  |> List.filter (fun clause ->
       not (List.exists (fun lit -> List.mem lit assign) clause))
  |> List.map (fun clause ->
       List.filter (fun lit -> not (List.mem (-lit) assign)) clause)

let find_unit_clause (f : Cnf.formula) : int option =
  match List.find_opt (fun clause -> List.length clause = 1) f with
  | Some [ lit ] -> Some lit
  | _ -> None

let rec unit_propagate (assign : int list) (f : Cnf.formula)
    : int list * Cnf.formula =
  let f = simplify assign f in
  match find_unit_clause f with
  | None -> (assign, f)
  | Some lit -> unit_propagate (lit :: assign) f

let find_pure_literal (f : Cnf.formula) : int option =
  let all_lits = List.concat f in
  List.find_opt
    (fun lit -> not (List.mem (-lit) all_lits))
    all_lits

type result = Sat of int list | Unsat

let pick_variable (assign : int list) (n : int) : int option =
  let assigned_vars = List.map abs assign in
  let rec go v =
    if v > n then None
    else if List.mem v assigned_vars then go (v + 1)
    else Some v
  in
  go 1

let rec search (assign : int list) (f : Cnf.formula) (n : int)
    : int list option =
  let (assign, f) = unit_propagate assign f in
  if Cnf.has_empty_clause f then
    None
  else if f = [] then
    Some assign
  else
    match find_pure_literal f with
    | Some lit -> search (lit :: assign) f n
    | None ->
      (match pick_variable assign n with
       | None -> Some assign
       | Some v ->
         (match search (v :: assign) f n with
          | Some result -> Some result
          | None -> search ((-v) :: assign) f n))

let model_satisfies (assign : int list) (f : Cnf.formula) : bool =
  List.for_all
    (fun clause -> List.exists (fun lit -> List.mem lit assign) clause)
    f

let solve (n : int) (f : Cnf.formula) : result =
  match search [] (restrict n f) n with
  | Some assign when model_satisfies assign f -> Sat assign
  | _ -> Unsat