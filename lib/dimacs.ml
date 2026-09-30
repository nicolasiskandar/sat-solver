exception Parse_error of string

let parse_clause_line (line : string) : Cnf.clause =
  line
  |> String.split_on_char ' '
  |> List.filter (fun s -> s <> "")
  |> List.map int_of_string
  |> List.filter (fun lit -> lit <> 0)

let parse_file (path : string) : int * Cnf.formula =
  let ic = open_in path in
  let num_vars = ref 0 in
  let clauses = ref [] in
  let current_clause = ref [] in
  (try
     while true do
       let line = input_line ic |> String.trim in
       if line = "" || line.[0] = 'c' then ()
       else if line.[0] = 'p' then begin
         match String.split_on_char ' ' line with
         | [ "p"; "cnf"; n; _ ] -> num_vars := int_of_string n
         | _ -> raise (Parse_error ("malformed problem line: " ^ line))
       end
       else begin
         let toks =
           line |> String.split_on_char ' '
                |> List.filter (fun s -> s <> "")
                |> List.map int_of_string
         in
         List.iter (fun tok ->
           if tok = 0 then begin
             clauses := List.rev !current_clause :: !clauses;
             current_clause := []
           end else
             current_clause := tok :: !current_clause
         ) toks
       end
     done
   with End_of_file -> close_in ic);
  (!num_vars, List.rev !clauses)