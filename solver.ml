open Core

module Dpll = struct
        type var = int
        type lit =
                | P of var
                | N of var
        type clause = lit list
        type expr = clause list

        let run expr =
                if complete expr then
                        true
                else if empty_clause expr then
                        false
                else
                        let expr = do_unit_propogations expr in
                        let expr = do_pure_literal_assigns expr in
                        let l = choose_literal expr in
                        (run ([P of l] :: expr)) or
                                (run ([N of l] :: expr))
end
