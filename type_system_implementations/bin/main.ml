open Common.Language_sig

let languages = [
    ("stlc", (module Stlc.Language.Language : LANGUAGE));
    ("stlc_noann", (module Stlc_noann.Language.Language : LANGUAGE));
    ("stlc_noann_onthefly", (module Stlc_noann_onthefly.Language.Language : LANGUAGE));
    ("bidir", (module Bidir.Language.Language : LANGUAGE));
    ("hindley_milner", (module Hindley_milner.Language.Language : LANGUAGE));
    ("cocontextual", (module Cocontextual.Language.Unrestricted : LANGUAGE));
    ("cocontextual_linear", (module Cocontextual.Language.Linear : LANGUAGE));
    ("linear_subtractive", (module Linear_subtractive.Language.Language : LANGUAGE));
    ("linear_additive", (module Linear_additive.Language.Language : LANGUAGE))
]

let () =
    if Array.length Sys.argv < 2 then
        let pp_comma ppf () = Format.pp_print_string ppf ", " in
        let lang_names = List.map fst languages in
        let err =
            Format.asprintf "Missing language name. Possible values: %s\n"
                (String.concat ", " lang_names)
        in
        failwith err
    else
        let lang_name = Sys.argv.(1) in
        let module Language =
            (val (
                match List.assoc_opt lang_name languages with
                    | Some lang -> lang
                    | None ->
                        let err =
                            Format.asprintf "No language implementation for %s" lang_name
                        in
                        failwith err
            ) : LANGUAGE)
        in
        let module Repl = Common.Repl.Make(Language) in
        Repl.repl ~prompt:lang_name ()
