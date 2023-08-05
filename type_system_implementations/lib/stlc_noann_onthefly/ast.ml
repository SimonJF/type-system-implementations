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
    
    let mk_var v = TVar v
    let mk_int = TInt
    let mk_bool = TBool
    let mk_string = TString
    let mk_unit = TUnit
    let mk_fun t1 t2 = TFun (t1, t2)

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
        | EFun of (binder * t)
        | EApp of (t * t)
        | EIf of (t * t * t)

    let mk_constant c = EConst c
    let mk_variable v = EVar v
    let mk_let x e1 e2 = ELet (x, e1, e2)
    let mk_bin_op op e1 e2 = EBinOp (op, e1, e2)
    let mk_fun x _ body = EFun (x, body)
    let mk_app e1 e2 = EApp (e1, e2)
    let mk_if cond t e = EIf (cond, t, e)
end