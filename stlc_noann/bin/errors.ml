exception Parse_error of string
exception Type_error of string

let parse_error str = Parse_error str
let type_error str = Type_error str
