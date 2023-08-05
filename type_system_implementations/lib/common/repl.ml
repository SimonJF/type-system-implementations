open Language_sig

module Make(Language: LANGUAGE) = struct
    open Language
    module MyParse = Parse.Make(Language)

    let pipeline str =
        let expr = MyParse.parse_string str () in
        Language.typecheck expr

    let rec repl ?(prompt="") () =
        TyVar.reset ();
        print_string (prompt ^ "> ");
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
