let resolve (c1 : Cnf.clause) (c2 : Cnf.clause) (v : int) : Cnf.clause =
  let without_v c = List.filter (fun lit -> abs lit <> v) c in
  List.sort_uniq compare (without_v c1 @ without_v c2)

let level_of (trail : Trail.t) (lit : int) : int option =
  match Trail.entry_of trail (abs lit) with
  | Some entry -> Some entry.level
  | None -> None

let pos_of (trail : Trail.t) (lit : int) : int =
  match Trail.entry_of trail (abs lit) with
  | Some entry -> entry.pos
  | None -> -1

let at_current_level (trail : Trail.t) (clause : Cnf.clause) : Cnf.clause =
  let current = Trail.current_level trail in
  List.filter
    (fun lit -> match level_of trail lit with
       | Some l -> l = current
       | None -> false)
    clause

let first_uip (trail : Trail.t) (conflict_clause : Cnf.clause) : Cnf.clause =
  let rec loop clause =
    match at_current_level trail clause with
    | [] | [ _ ] -> clause
    | candidates ->
      let pivot =
        List.fold_left
          (fun best l -> if pos_of trail l > pos_of trail best then l else best)
          (List.hd candidates) candidates
      in
      (match Trail.entry_of trail (abs pivot) with
       | Some { reason = Propagated reason; _ } ->
         loop (resolve clause reason (abs pivot))
       | _ ->
         failwith
           "Conflict_analysis: current-level literal without a reason clause")
  in
  loop conflict_clause

let analyze (trail : Trail.t) (conflict_clause : Cnf.clause) : Cnf.clause * int =
  let current = Trail.current_level trail in
  let learned = first_uip trail conflict_clause in
  let key lit = match level_of trail lit with Some l -> l | None -> -1 in
  let learned =
    List.sort
      (fun a b -> match compare (key b) (key a) with 0 -> compare a b | c -> c)
      learned
  in
  let backjump_level =
    List.fold_left
      (fun acc lit -> if key lit = current then acc else max acc (key lit))
      0 learned
  in
  (learned, backjump_level)