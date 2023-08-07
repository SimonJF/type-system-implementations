(* STLC: Basic typechecker for the simply-typed lambda calculus.
   No constraints necessary, but all lambdas must be annotated. *)
open Ast
open Common
open Language_sig
open Common_types

module Typecheck = struct
    module StringMap = Map.Make(String)

    type env = Type.t StringMap.t

    (* Typechecking: constructs a type and constraint set *)
    let rec tc env =
        let open Expr in
        let open Type in
        let tc_const = function
            | Constant.CString _ -> TString
            | Constant.CBool _ -> TBool
            | Constant.CInt _ -> TInt
            | Constant.CUnit -> TUnit
        in
        let tc_binop op e1 e2 =
            let open BinOp in
            let ty1 = tc env e1 in
            let ty2 = tc env e2 in
            match op with
                | And | Or ->
                    if (ty1 <> Type.TBool || ty2 <> Type.TBool) then
                        raise (Errors.type_error "Arguments to && or || must both be booleans.")
                    else TBool
                (* Polymorphic equality *)
                | Eq | NEq ->
                    if (ty1 <> ty2) then
                        raise (Errors.type_error "Arguments to == or != must be of the same type.")
                    else TBool
                (* Relational numeric operators *)
                | LT | GT | LEq | GEq ->
                    if (ty1 <> Type.TInt || ty2 <> Type.TInt) then
                        raise (Errors.type_error "Arguments to relational numeric operations must be Int.")
                    else TBool
                (* Numeric operators *)
                | Add | Mul | Sub | Div ->
                    if (ty1 <> Type.TInt || ty2 <> Type.TInt) then
                        raise (Errors.type_error "Arguments to numeric operations must be Int.")
                    else TInt
                in
        function
            | EVar v -> StringMap.find v env
            | EFun (bnd, ty, body) ->
                let env' = StringMap.add bnd ty env in
                let body_ty = tc env' body in
                TFun (ty, body_ty)
            | EApp (e1, e2) ->
                let ty_fun = tc env e1 in
                let ty_arg = tc env e2 in
                begin
                    match ty_fun with
                        | TFun (ty1, ty2) ->
                            if ty_arg <> ty1 then
                                let err =
                                    Format.asprintf
                                        "Argument type mismatch: required %a but got %a"
                                        Type.pp ty1
                                        Type.pp ty_arg
                                in
                                raise (Errors.type_error err)
                            else ty2
                        | _ ->
                            let err =
                                Format.asprintf
                                    "Tried to apply non-function with type %a"
                                    Type.pp ty_fun
                            in
                            raise (Errors.type_error err)
                end
            | EBinOp (op, e1, e2) -> tc_binop op e1 e2
            | EConst c -> tc_const c
            | ELet (bnd, e1, e2) ->
                let ty1 = tc env e1 in
                let env' = StringMap.add bnd ty1 env in
                let ty2 = tc env' e2 in
                ty2
            | EAnn (e, ann) ->
                let ty = tc env e in
                let () =
                    if (ty <> ann) then
                        let err =
                            Format.asprintf
                                "Type of expression didn't match annotation. Expected %a but got %a."
                                Type.pp ann
                                Type.pp ty
                        in
                        raise (Errors.type_error err)
                in
                ty
            | EIf (e1, e2, e3) ->
                let ty1 = tc env e1 in
                let ty2 = tc env e2 in
                let ty3 = tc env e3 in
                let () =
                    if ty1 <> Type.TBool then
                        raise (Errors.type_error "The condition of an 'if' must have type Bool")
                in
                let () =
                    if ty2 <> ty3 then
                        raise (Errors.type_error "Both branches of a conditional must have the same type")
                in
                ty2
                
    let typecheck expr = tc StringMap.empty expr
end

module Language : LANGUAGE = struct
    module Type = Type
    module Expr = Expr

    module Type_constructors = struct
        open Type
        let mk_int = TInt
        let mk_bool = TBool
        let mk_string = TString
        let mk_unit = TUnit
        let mk_fun t1 t2 = TFun (t1, t2)
        let mk_pair _ _ = raise (Errors.unsupported "pair")
    end

    module Expr_constructors = struct
        open Expr

        let mk_constant c = EConst c
        let mk_variable v = EVar v
        let mk_let x e1 e2 = ELet (x, e1, e2)
        let mk_bin_op op e1 e2 = EBinOp (op, e1, e2)
        let mk_fun x ty body =
            match ty with
                | Some ty -> EFun (x, ty, body)
                | None -> raise (Common.Errors.parse_error "In STLC, all binders must be annotated")
        let mk_app e1 e2 = EApp (e1, e2)
        let mk_ann e t = EAnn (e, t)
        let mk_if cond t e = EIf (cond, t, e)
        let mk_fst _ = raise (Errors.unsupported "fst")
        let mk_snd _ = raise (Errors.unsupported "snd")
        let mk_letpair _ _ _ _ = raise (Errors.unsupported "letpair")
        let mk_pair _ _ = raise (Errors.unsupported "pair")
    end

    let typecheck = Typecheck.typecheck
    (* No state to reset *)
    let reset_state () = ()
end
