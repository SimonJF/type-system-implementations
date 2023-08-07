open Common.Common_types

module TyVar = struct
    type t = string
    let source = ref 0
    
    let reset () = source := 0

    let fresh ?(prefix="_") () =
        let sym = !source in
        let () = incr source in
        prefix ^ (string_of_int sym)

    let pp = Format.pp_print_string
end

module Type = struct
    type tyvar = TyVar.t
    type t =
        | TVar of TyVar.t
        | TInt
        | TBool
        | TString
        | TUnit
        | TFun of (t * t)
        | TPair of (t * t)

    let rec pp ppf =
        function
            | TVar tv -> TyVar.pp ppf tv
            | TInt -> Format.pp_print_string ppf "Int"
            | TBool -> Format.pp_print_string ppf "Bool"
            | TString -> Format.pp_print_string ppf "String"
            | TUnit -> Format.pp_print_string ppf "Unit"
            | TFun (t1, t2) -> Format.fprintf ppf "(%a -> %a)" pp t1 pp t2
            | TPair (t1, t2) -> Format.fprintf ppf "(%a * %a)" pp t1 pp t2

    let fresh_var () = TVar (TyVar.fresh ())
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
        | EFun of (binder * ty option * t)
        | EApp of (t * t)
        | EAnn of (t * ty)
        | EIf of (t * t * t)
        | EPair of (t * t)
        | ELetPair of (variable * variable * t * t)
        | EFst of t
        | ESnd of t
end
