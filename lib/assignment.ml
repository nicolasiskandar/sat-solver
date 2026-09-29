type value = True | False | Unassigned

type t = { table : value array }

let create n { table = Array.make (n + 1) Unassigned }

let value_of t v = t.table.(v)

let set t v b =
  t.table.(v) <- (if b then True else False)

let unset t v =
  t.table.(v) <- Unassigned

let is_fully_assigned t =
  let n = Array.length t.table in
  let rec check i =
    i >= n || (t.table.(i) <> Unassigned && check (i + 1))
  in
  check 1