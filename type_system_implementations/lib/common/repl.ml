open Language_sig

module Make(Language: LANGUAGE) = struct
    open Language
    module MyParse = Parse.Make(Language)

    let pipeline str =
        let expr = MyParse.parse_string str () in
        Language.typecheck expr

    let rec repl ?(prompt="") () =
        Language.reset_state ();
        print_string (prompt ^ "> ");
        let str = read_line () in
        let () =
            let open Errors in
            try
                let ty = pipeline str in
                Format.printf "Type: %a\n" Type.pp ty
            with
                | Parse_error err ->
                    Format.printf "[Parse error] %s\n" err
                | Type_error err ->
                    Format.printf "[Type error] %s\n" err
                | Unsupported feat ->
                    Format.printf 
                        "[Unsupported] Feature %s is unsupported in language %s\n"
                        feat prompt
                | exn -> Format.printf "[Error] %s\n" (Printexc.to_string exn)
        in
        let () = Format.print_flush () in
        repl ~prompt ()
 
end
