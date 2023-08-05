open Common.Common_types

(* Main difference here is that type variables also contain a union-find point. *)
module Type = struct
    type resolution_state =  Unresolved | Resolved of t
    and tyvar = string * (resolution_state UnionFind.elem)
    and t =
        | TVar of tyvar
        | TInt
        | TBool
        | TString
        | TUnit
        | TFun of (t * t)

    module TyVar = struct
        let source = ref 0
        let reset () = source := 0

        let fresh ?(prefix="_") () =
            let sym = !source in
            let () = incr source in
            let point = UnionFind.make Unresolved in
            prefix ^ (string_of_int sym), point

        let pp ppf (tv, _) = Format.pp_print_string ppf tv
        let point = snd
        let compare (tv1, _) (tv2, _) = String.compare tv1 tv2
    end

    let rec pp ppf =
        function
            | TVar tv -> TyVar.pp ppf tv
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
        | EFun of (binder * ty option * t)
        | EApp of (t * t)
        | EIf of (t * t * t)
end
