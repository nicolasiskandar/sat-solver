type clause = { lits : int array; mutable w1 : int; mutable w2 : int }

let dummy = { lits = [||]; w1 = 0; w2 = 0 }

type t = {
  n : int;
  buckets : int list array;
  mutable store : clause array;
  mutable count : int;
}

let create n () =
  let n = max 0 n in
  { n; buckets = Array.make (2 * n + 1) []; store = Array.make 16 dummy; count = 0 }

let index_of n lit = lit + n

let add_watch t id lit =
  let i = index_of t.n lit in
  t.buckets.(i) <- id :: t.buckets.(i)

let remove_watch t id lit =
  let i = index_of t.n lit in
  t.buckets.(i) <- List.filter (fun c -> c <> id) t.buckets.(i)

let grow t =
  let bigger = Array.make (2 * Array.length t.store) dummy in
  Array.blit t.store 0 bigger 0 t.count;
  t.store <- bigger

let watches_of (c : Cnf.clause) : (int * int) option =
  match c with
  | [] -> None
  | [ l ] -> Some (l, 0)
  | l1 :: l2 :: _ -> Some (l1, l2)

let add (t : t) (c : Cnf.clause) : int option =
  match watches_of c with
  | None -> None
  | Some (w1, w2) ->
    List.iter
      (fun l ->
        let i = index_of t.n l in
        assert (i >= 0 && i < Array.length t.buckets))
      c;
    if t.count = Array.length t.store then grow t;
    let id = t.count in
    t.count <- id + 1;
    t.store.(id) <- { lits = Array.of_list c; w1; w2 };
    add_watch t id w1;
    if w2 <> 0 then add_watch t id w2;
    Some id

let watched_by t lit = t.buckets.(index_of t.n lit)

let watched t id =
  let c = t.store.(id) in
  (c.w1, c.w2)

let lits t id = t.store.(id).lits

let move_watch t id ~from_ ~to_ =
  let c = t.store.(id) in
  if c.w1 = from_ then c.w1 <- to_
  else if c.w2 = from_ then c.w2 <- to_
  else failwith "Watch_list.move_watch: literal is not watched by that clause";
  remove_watch t id from_;
  add_watch t id to_

let to_clause t id = Array.to_list t.store.(id).lits

let num_clauses t = t.count
