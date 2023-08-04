module TyVar = struct
    type t = string
    let source = ref 0
    
    let reset () = source := 0

    let fresh ?(prefix="_") () =
        let sym = !source in
        let () = incr source in
        prefix ^ (string_of_int sym)

    let pp = Format.pp_print_string
    let compare str = String.compare
end

module Type = struct
    type t =
        | TVar of TyVar.t
        | TInt
        | TBool
        | TString
        | TUnit
        | TFun of (t * t)


    let rec pp ppf =
        function
            | TVar tv -> TyVar.pp ppf tv
            | TInt -> Format.pp_print_string ppf "Int"
            | TBool -> Format.pp_print_string ppf "Bool"
            | TString -> Format.pp_print_string ppf "String"
            | TUnit -> Format.pp_print_string ppf "Unit"
            | TFun (t1, t2) -> Format.fprintf ppf "(%a -> %a)" pp t1 pp t2
end

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

module Expr = struct
    type binder = string
    type variable = string

    type t =
        | EVar of variable
        | EConst of Constant.t
        | ELet of (binder * t * t)
        | EBinOp of (BinOp.t * t * t)
        | EFun of (binder * t)
        | EApp of (t * t)
        | EIf of (t * t * t)
end

