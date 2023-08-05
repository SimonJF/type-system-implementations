open Ast_sig

module Make
        (Ast: AST)
        (Typecheck: sig val typecheck : Ast.Expr.t -> Ast.Type.t end)
        = struct

    open Ast

    module MyParse = Parse.Make(Ast)

    let pipeline str =
        let expr = MyParse.parse_string str () in
        Typecheck.typecheck expr

    let rec repl () =
        TyVar.reset ();
        print_newline ();
        print_string "> ";
        let str = read_line () in
        let () =
            let open Errors in
            try
                let ty = pipeline str in
                Format.printf "Solved type: %a\n" Type.pp ty
            with
                | Parse_error err ->
                    Format.printf "[Parse error] %s\n" err
                | Type_error err ->
                    Format.printf "[Type error] %s\n" err
                | exn -> Format.printf "[Error] %s\n" (Printexc.to_string exn)
        in
        let () = Format.print_flush () in
        repl ()
 
end
