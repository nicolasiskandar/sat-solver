type t = { activity : float array; bump_amount : float; decay_factor : float }

let create n =
  let n = max 0 n in
  { activity = Array.make (n + 1) 0.; bump_amount = 1.0 /. 0.95; decay_factor = 0.95 }

let bump t v =
  if v >= 1 && v < Array.length t.activity then
    t.activity.(v) <- t.activity.(v) +. t.bump_amount

let decay_all t =
  for v = 1 to Array.length t.activity - 1 do
    t.activity.(v) <- t.activity.(v) *. t.decay_factor
  done

let best_unassigned t is_assigned =
  let best = ref None in
  for v = 1 to Array.length t.activity - 1 do
    if not (is_assigned v) then
      let a = t.activity.(v) in
      match !best with
      | None -> best := Some (v, a)
      | Some (_, best_a) when a > best_a -> best := Some (v, a)
      | Some _ -> ()
  done;
  match !best with None -> None | Some (v, _) -> Some v
