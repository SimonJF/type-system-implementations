(* bidir: Basic bidirectional typechecking. *)
open Ast
open Common
open Language_sig
open Common_types

module Typecheck = struct
    module StringMap = Map.Make(String)

    type env = Type.t StringMap.t

    let const_ty =
        let open Type in
        function
            | Constant.CString _ -> TString
            | Constant.CBool _ -> TBool
            | Constant.CInt _ -> TInt
            | Constant.CUnit -> TUnit

    let type_mismatch expected actual =
        let err =
            Format.asprintf "Type mismatch: expected %a but got %a"
                Type.pp expected Type.pp actual
        in
        raise (Errors.type_error err)

    let type_mismatch_str expected actual =
        let err =
            Format.asprintf "Type mismatch: expected %s but got %a"
                expected Type.pp actual
        in
        raise (Errors.type_error err)

    let rec check env e ty =
        let open Expr in
        let open Type in
        match e with
            | EFun (bnd, body) ->
                begin
                    match ty with
                        | TFun (ty_arg, ty_result) ->
                            let env' = StringMap.add bnd ty_arg env in
                            check env' body ty_result
                        | _ ->
                            type_mismatch_str "a function type" ty
                end
            | _ ->
                let synth_ty = synth env e in
                if synth_ty <> ty then
                    type_mismatch ty synth_ty
    and synth_binop env op e1 e2 =
        let open BinOp in
        match op with
            | And | Or ->
                check env e1 Type.TBool;
                check env e2 Type.TBool;
                Type.TBool
            (* Polymorphic equality *)
            | Eq | NEq ->
                let ty = synth env e1 in
                check env e2 ty;
                Type.TBool
            (* Relational numeric operators *)
            | LT | GT | LEq | GEq ->
                check env e1 Type.TInt;
                check env e2 Type.TInt;
                Type.TBool
            (* Numeric operators *)
            | Add | Mul | Sub | Div ->
                check env e1 Type.TInt;
                check env e2 Type.TInt;
                Type.TInt
    and synth env e =
        let open Expr in
        let open Type in
        match e with
            | EVar v -> StringMap.find v env
            | EConst c -> const_ty c
            | EBinOp (op, e1, e2) -> synth_binop env op e1 e2
            | EApp (e1, e2) ->
                let ty_fun = synth env e1 in
                begin
                    match ty_fun with
                        | TFun (ty1, ty2) ->
                            check env e2 ty1;
                            ty2
                        | ty ->
                            let err =
                                Format.asprintf "Synthesised non-function type %a in application"
                                    Type.pp ty
                            in
                            raise (Errors.type_error err)
                end
            | EAnn (e, ann) ->
                check env e ann;
                ann
            | ELet (bnd, e1, e2) ->
                let ty1 = synth env e1 in
                let env' = StringMap.add bnd ty1 env in
                let ty2 = synth env' e2 in
                ty2
            | EIf (e1, e2, e3) ->
                check env e1 Type.TBool;
                let ty = synth env e2 in
                check env e3 ty;
                ty
            | _ ->
                (* TODO: Probably want to implement a pretty printer so the
                   error will be slightly better *)
                raise (Errors.type_error "Could not synthesise type")
                
    let typecheck expr = synth StringMap.empty expr
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
    end

    module Expr_constructors = struct
        open Expr

        let mk_constant c = EConst c
        let mk_variable v = EVar v
        let mk_let x e1 e2 = ELet (x, e1, e2)
        let mk_bin_op op e1 e2 = EBinOp (op, e1, e2)
        let mk_fun x ty body =
            match ty with
                | Some _ -> 
                    raise (Common.Errors.parse_error
                        "Lambda annotations not supported in bidir; add an annotation to the whole function instead")
                | None -> EFun (x, body)
        let mk_app e1 e2 = EApp (e1, e2)
        let mk_ann e t = EAnn (e, t)
        let mk_if cond t e = EIf (cond, t, e)
    end

    let typecheck = Typecheck.typecheck
    (* No state to reset *)
    let reset_state () = ()
end
