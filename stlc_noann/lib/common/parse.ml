open Lexer
open Lexing
open Language_sig

module Make(Language : LANGUAGE) = struct
    module MyParser = Parser.Make(Language)

    let print_position ppf lexbuf =
      let pos = lexbuf.lex_curr_p in
      Format.fprintf ppf "%s:%d:%d" pos.pos_fname
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

    let parse_with_error lexbuf =
      try MyParser.expr_main Lexer.token lexbuf with
      | Lexical_error msg ->
        let msg = Format.asprintf "%a: %s" print_position lexbuf msg in
        raise (Errors.parse_error msg)
      | MyParser.Error ->
        let msg = Format.asprintf "%a: syntax error" print_position lexbuf in
        raise (Errors.parse_error msg)

    let parse_file filename () =
      let inx = In_channel.open_text filename in
      let lexbuf = Lexing.from_channel inx in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      let expr = parse_with_error lexbuf in
      In_channel.close inx;
      expr

    let parse_string x () =
      let lexbuf = Lexing.from_string x in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "<string>" };
      let expr = parse_with_error lexbuf in
      expr
end
