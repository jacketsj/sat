open Core
open Async

module Cnf = struct
  (* type variable = int [@@deriving sexp_of] *)

  (* type literal = Pos of variable | Neg of variable [@@deriving sexp_of] *)
  type literal = int [@@deriving sexp_of]

  type clause = literal list [@@deriving sexp_of]

  type expression = clause list [@@deriving sexp_of]

  let parse_variable str = int_of_string str

  let parse_literal str =
    let remove_first str = String.sub str ~pos:1 ~len:(String.length str - 1) in
    match str.[0] with
    | '-' -> -parse_variable (remove_first str)
    | '+' -> parse_variable (remove_first str)
    | _ -> parse_variable str

  let parse_clause str = List.map (String.split str ~on:' ') ~f:(fun literal_str -> parse_literal literal_str)

  let parse_expr str_list = List.map str_list ~f:parse_clause

  let parse_input_file input_file =
    let lines = In_channel.read_lines input_file in
    parse_expr lines
end

module Solution = struct
  type t = Sat of int list | Unsat [@@deriving sexp]
end

module Dpll = struct
  type assignment = int list

  let assignment_complete assignment = List.fold assignment ~init:true ~f:(fun acc elem -> acc && elem = 1)

  let empty_clause expr = List.fold expr ~init:false ~f:(fun acc clause -> acc || List.is_empty clause)

  let first_if_only_one l = match l with [] | _ :: _ :: _ -> None | [first] -> Some first

  let get_units expr =
    List.fold expr ~init:[] ~f:(fun acc clause ->
        match first_if_only_one clause with None -> acc | Some x -> x :: acc)

  let do_unit_propogations expr =
    let units = get_units expr in
    List.map expr ~f:(fun clause ->
        List.filter clause ~f:(fun literal ->
            List.fold units ~init:true ~f:(fun acc unit_var -> acc || literal = -unit_var)))

  let rec assign_next_var assignment sign =
    match assignment with
    | [] ->
        print_s [%message "over-assigned to vars"] ;
        assignment
    | 0 :: tl -> sign :: tl
    | hd :: tl -> hd :: assign_next_var tl sign

  let empty_assignment expr =
    let rec var_count expr acc =
      let rec var_count_clause clause acc =
        match clause with [] -> acc | hd :: tl -> var_count_clause tl (max acc hd)
      in
      match expr with [] -> acc | clause :: rest -> var_count rest (var_count_clause clause acc)
    in
    let rec empty_assignment count acc = if count = 0 then acc else empty_assignment (count - 1) (0 :: acc) in
    empty_assignment (var_count expr 0) []

  let run expr =
    let rec run (expr : Cnf.expression) (assignment : assignment) =
      let _ = failwith (Sexp.to_string_hum (List.sexp_of_t (List.sexp_of_t Int.sexp_of_t) expr)) in
      let expr = do_unit_propogations expr in
      (* let assignment = do_pure_literal_assignments expr assignment in *)
      if empty_clause expr then Solution.Unsat
      else if assignment_complete assignment then
        let _ = failwith (Sexp.to_string_hum (Solution.sexp_of_t (Solution.Sat assignment))) in
        Solution.Sat assignment
      else
        let assignment_t = assign_next_var assignment 1 in
        let assignment_f = assign_next_var assignment 0 in
        match run expr assignment_t with Unsat -> run expr assignment_f | x -> x
    in
    run expr (empty_assignment expr)

  (* let run expr =
                if complete expr then
                        true
                else if empty_clause expr then
                        false
                else
                        let expr = do_unit_propogations expr in
                        let expr = do_pure_literal_assigns expr in
                        let l = choose_literal expr in
                        (run ([P of l] :: expr)) or
                                (run ([N of l] :: expr)) *)

  let command =
    Command.basic ~summary:"Run the DPLL algorithm on a given input string"
      (let open Command.Let_syntax in
      let%map_open input_file = anon ("INPUT FILE" %: string) in
      fun () ->
        print_string "opening file\n" ;
        print_s [%sexp (run (Cnf.parse_input_file input_file) : Solution.t)])
end

let command = Command.group ~summary:"A small OCaml SAT solver" [("dpll", Dpll.command)]

let () = Command.run command
