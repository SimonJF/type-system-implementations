{
  open Lexing
  open Tokens

  exception Lexical_error of string

  let comments = ref 0;;

  let open_comment () =
    comments := !comments+1
  ;;

  let close_comment () =
    comments := !comments-1;
    !comments > 0
  ;;

  let reset_comments () =
    comments := 1
  ;;
}

rule token = parse
  | [' ' '\t' '\r' '\n']*
      { token lexbuf }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | '('
      { LPAREN }
  | ')'
      { RPAREN }
  | '.' { DOT }
  | '*'      { STAR }
  | '/'      { DIV }
  | '+'      { PLUS }
  | '-'      { MINUS }
  | ':'      { COLON }
  | "&&"     { AND }
  | "||"     { OR }
  | ">="     { GEQ }
  | "<"      { LT }
  | ">"      { GT }
  | "<="     { LEQ }
  | "=="     { EQQ }
  | "!="     { NEQ }
  | '='
      { EQ }
  | "->"
      { ARROW }
  | "*)"
      { raise (Lexical_error "Unmatched end of comment") }
  | "(*"
      {
        reset_comments ();
        comment lexbuf;
        token lexbuf
      }
  | "\\"
      { LAMBDA }
  | "let"
      { LET }
  | "in"
      { IN }
  | "true"
      { TRUE }
  | "false"
      { FALSE }
  | "if"
      { IF }
  | "then"
      { THEN }
  | "else"
      { ELSE }
  | "String"
      { STRING }
  | "Int"
      { INT }
  | "Bool"
      { BOOL }
  | "Unit"
      { UNIT }
  | "()"
      { UNITV }
  | ['0'-'9']+
      { INTV (int_of_string (lexeme lexbuf)) }
  | ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*
      { ID (lexeme lexbuf) }
  | eof
      { EOF }
  | _
      { raise (Lexical_error ("Illegal character " ^ lexeme lexbuf)) }

and read_string buf =
    parse
    | '"'       { STRINGV (Buffer.contents buf) }
    | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
    | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
    | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
    | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
    | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
    | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
    | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
    | [^ '"' '\\']+
      { Buffer.add_string buf (Lexing.lexeme lexbuf);
        read_string buf lexbuf
      }
    | _ { raise (Lexical_error ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
    | eof { raise (Lexical_error ("String is not terminated")) }
and comment = parse
  | "(*"
      {
        open_comment ();
        comment lexbuf
      }
  | "*)"
      { if close_comment () then comment lexbuf }
  | eof
      { raise (Lexical_error "Comment not terminated") }
  | _
      { comment lexbuf }
