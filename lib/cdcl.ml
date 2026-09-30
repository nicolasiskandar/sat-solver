type result = Sat of int list | Unsat

type inspection = Skipped | Rewatched | Implies of int | Falsified

let inspect (trail : Trail.t) (watchers : Watch_list.t) (falsified : int) (id : int)
    : inspection =
  let w1, w2 = Watch_list.watched watchers id in
  if w2 = 0 then Falsified
  else
    let other = if w1 = falsified then w2 else w1 in
    match Trail.value trail other with
    | Some true -> Skipped
    | Some false ->
      let lits = Watch_list.lits watchers id in
      let is_live l = Trail.value trail l <> Some false in
      (match Array.to_list lits |> List.find_opt is_live with
       | Some l ->
         Watch_list.move_watch watchers id ~from_:other ~to_:l;
         Rewatched
       | None -> Falsified)
    | None ->
      let lits = Watch_list.lits watchers id in
      let is_candidate l = l <> other && Trail.value trail l <> Some false in
      (match Array.to_list lits |> List.find_opt is_candidate with
       | Some l ->
         Watch_list.move_watch watchers id ~from_:falsified ~to_:l;
         Rewatched
       | None -> Implies other)

let propagate (trail : Trail.t) (watchers : Watch_list.t) (queue : int list)
    : int option =
  let queue = ref (List.rev queue) in
  let conflict = ref None in
  while !queue <> [] && !conflict = None do
    let p = List.hd !queue in
    queue := List.tl !queue;
    let falsified = -p in
    List.iter
      (fun id ->
         if !conflict = None then
           match inspect trail watchers falsified id with
           | Skipped | Rewatched -> ()
           | Implies other ->
             Trail.push_propagated trail other (Watch_list.to_clause watchers id);
             queue := other :: !queue
           | Falsified -> conflict := Some id)
      (Watch_list.watched_by watchers falsified)
  done;
  !conflict

let assigned_lits (trail : Trail.t) : int list =
  List.map (fun (entry : Trail.entry) -> entry.lit) (Trail.entries trail)

let normalize_clause (c : Cnf.clause) : Cnf.clause option =
  let lits = List.sort_uniq compare c in
  if List.exists (fun lit -> List.mem (-lit) lits) lits then None else Some lits

let solve (n : int) (formula : Cnf.formula) : result =
  let formula = Dpll.restrict n formula |> List.filter_map normalize_clause in
  let trail = Trail.create n in
  let watchers = Watch_list.create n () in
  let vsids = Vsids.create n in
  let rec attach = function
    | [] -> true
    | c :: rest -> Watch_list.add watchers c <> None && attach rest
  in
  if not (attach formula) then Unsat
  else
    let rec imply_units = function
      | [] -> Some []
      | c :: rest -> (
        match c with
        | [ lit ] -> (
          match Trail.value trail lit with
          | Some true -> imply_units rest
          | Some false -> None
          | None ->
            Trail.push_propagated trail lit c;
            (match imply_units rest with
             | Some rest -> Some (lit :: rest)
             | None -> None))
        | _ -> imply_units rest)
    in
    match imply_units formula with
    | None -> Unsat
    | Some implied ->
      let is_assigned v = Trail.entry_of trail v <> None in
      let rec search queue =
        match propagate trail watchers queue with
        | Some id ->
          if Trail.current_level trail = 0 then Unsat
          else
            let (learned, backjump_level) =
              Conflict_analysis.analyze trail (Watch_list.to_clause watchers id)
            in
            if learned = [] then Unsat
            else begin
              ignore (Watch_list.add watchers learned);
              List.iter (fun lit -> Vsids.bump vsids (abs lit)) learned;
              Vsids.decay_all vsids;
              Trail.undo_to_level trail backjump_level;
              let unassigned =
                List.filter (fun lit -> Trail.entry_of trail (abs lit) = None) learned
              in
              match unassigned with
              | [ lit ] ->
                Trail.push_propagated trail lit learned;
                search [ lit ]
              | _ -> search []
            end
        | None ->
          (match Vsids.best_unassigned vsids is_assigned with
           | None ->
             let model = assigned_lits trail in
             if Cnf.satisfies model formula then Sat model else Unsat
           | Some v ->
             Trail.push_decision trail v;
             search (v :: queue))
      in
      search implied