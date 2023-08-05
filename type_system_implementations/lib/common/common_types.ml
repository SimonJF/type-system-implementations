module Constant = struct
    type t =
        | CString of string
        | CBool of bool
        | CInt of int
        | CUnit
end

module BinOp = struct
    type t = 
        | Add
        | Sub
        | Mul
        | Div
        | LT
        | GT
        | LEq
        | GEq
        | Eq
        | NEq
        | And
        | Or
end


