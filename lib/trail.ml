type reason = Decision | Propagated of Cnf.clause

type entry = { lit : int; level : int; pos : int; reason : reason }

type t = {
  mutable stack : entry list;
  mutable level : int;
  mutable next_pos : int;
  assignments : entry option array;
}

let create n =
  let n = max 0 n in
  { stack = []; level = 0; next_pos = 0; assignments = Array.make (n + 1) None }

let current_level t = t.level

let push_entry t level lit reason =
  let entry = { lit; level; pos = t.next_pos; reason } in
  t.next_pos <- t.next_pos + 1;
  t.stack <- entry :: t.stack;
  let v = abs lit in
  if v >= 1 && v < Array.length t.assignments then
    t.assignments.(v) <- Some entry;
  entry

let push_decision t lit =
  t.level <- t.level + 1;
  ignore (push_entry t t.level lit Decision)

let push_propagated t lit clause =
  ignore (push_entry t t.level lit (Propagated clause))

let entries t = List.rev t.stack

let entry_of t v =
  if v >= 1 && v < Array.length t.assignments then t.assignments.(v) else None

let value t lit =
  match entry_of t (abs lit) with
  | None -> None
  | Some entry -> Some (entry.lit = lit)

let undo_to_level t target_level =
  assert (target_level <= t.level);
  let kept, dropped =
    List.partition (fun (e : entry) -> e.level <= target_level) t.stack
  in
  List.iter
    (fun (e : entry) -> t.assignments.(abs e.lit) <- None)
    dropped;
  t.stack <- kept;
  t.level <- target_level
