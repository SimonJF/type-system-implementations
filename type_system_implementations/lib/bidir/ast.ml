open Common.Common_types

module Type = struct
    type t =
        | TInt
        | TBool
        | TString
        | TUnit
        | TFun of (t * t)

    let rec pp ppf =
        function
            | TInt -> Format.pp_print_string ppf "Int"
            | TBool -> Format.pp_print_string ppf "Bool"
            | TString -> Format.pp_print_string ppf "String"
            | TUnit -> Format.pp_print_string ppf "Unit"
            | TFun (t1, t2) -> Format.fprintf ppf "(%a -> %a)" pp t1 pp t2
end

module Expr = struct
    type ty = Type.t
    type binder = string
    type variable = string

    type t =
        | EVar of variable
        | EConst of Constant.t
        | ELet of (binder * t * t)
        | EBinOp of (BinOp.t * t * t)
        | EFun of (binder * t)
        | EApp of (t * t)
        | EAnn of (t * ty)
        | EIf of (t * t * t)
end
