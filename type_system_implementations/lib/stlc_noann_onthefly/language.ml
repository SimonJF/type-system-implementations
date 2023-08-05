(* stlc_noann_onthefly: Same as stlc_noann, but performs unification on-the-fly
   rather than waiting until the end. *)
open Ast
open Common
open Language_sig
open Common_types

module Constraint = struct
    type t = Type.t * Type.t

    let make t1 t2 = (t1, t2)
    let compare = Stdlib.compare
    let pp ppf (t1, t2) =
        Format.fprintf ppf "%a = %a" Type.pp t1 Type.pp t2
end

module ConstraintSet = struct
    include Set.Make(Constraint)
    let union_many = List.fold_left (union) empty
    let make_singleton t1 t2 = singleton (Constraint.make t1 t2)

    let pp ppf set =
        let pp_semi ppf () = Format.pp_print_string ppf "; " in
        let xs = elements set in
        Format.pp_print_list
            ~pp_sep:pp_semi
            Constraint.pp ppf xs
end

module Typecheck = struct
    module StringMap = Map.Make(String)
    type env = Type.t StringMap.t
    exception Occurs_check

    (* Checks whether type variable tv occurs in type t *)
    let occurs_check tv ty =
        let open Type in
        let rec go =
            function
                | TVar tv' ->
                    if tv = tv' then
                        raise Occurs_check
                | TFun (t1, t2) -> go t1; go t2
                | _ -> ()
        in
        try go ty with
            | Occurs_check ->
                let err =
                    Format.asprintf "Occurs check failed: %a occurs in %a"
                        TyVar.pp tv
                        Type.pp ty
                in
                raise (Errors.type_error err)

    let rec unify t1 t2 =
        let open Type in
        match t1, t2 with
             | t1, t2 when t1 = t2 -> ()
             | TFun (ta1, ta2), TFun (tb1, tb2) ->
                unify ta1 tb1; unify ta2 tb2
             | TVar tv, t
             | t, TVar tv ->
                 occurs_check tv t;
                 let pt = TyVar.point tv in
                 begin
                     match UnionFind.get pt with
                        | Unresolved -> UnionFind.set pt (Resolved t)
                        | Resolved t2 -> unify t2 t
                 end
            | _, _ ->
                let err =
                    Format.asprintf "Cannot unify %a with %a"
                        Type.pp t1
                        Type.pp t2
                in
                raise (Errors.type_error err)

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
                    unify ty1 Type.TBool;
                    unify ty2 Type.TBool;
                    TBool
                (* Polymorphic equality *)
                | Eq | NEq ->
                    unify ty1 ty2;
                    TBool
                (* Relational numeric operators *)
                | LT | GT | LEq | GEq ->
                    unify ty1 Type.TInt;
                    unify ty2 Type.TInt;
                    TBool
                (* Numeric operators *)
                | Add | Mul | Sub | Div ->
                    unify ty1 Type.TInt;
                    unify ty2 Type.TInt;
                    TInt
        in
        function
            | EVar v -> StringMap.find v env
            | EFun (bnd, ty_opt, body) ->
                (* If we have a type annotation, use that --
                   otherwise create fresh type variable *)
                let arg_ty =
                    match ty_opt with
                        | Some ann -> ann
                        | None -> TVar (TyVar.fresh ())
                in
                let env' = StringMap.add bnd arg_ty env in
                let body_ty = tc env' body in
                TFun (arg_ty, body_ty)
            | EApp (e1, e2) ->
                let ftv = TVar (TyVar.fresh ()) in
                let ty1 = tc env e1 in
                let ty2 = tc env e2 in
                unify ty1 (TFun (ty2, ftv));
                ftv
            | EBinOp (op, e1, e2) -> tc_binop op e1 e2
            | EConst c -> tc_const c
            | ELet (bnd, e1, e2) ->
                let ty1 = tc env e1 in
                let env' = StringMap.add bnd ty1 env in
                let ty2 = tc env' e2 in
                ty2
            | EIf (e1, e2, e3) ->
                let ty1 = tc env e1 in
                let ty2 = tc env e2 in
                let ty3 = tc env e3 in
                unify ty1 TBool;
                unify ty2 ty3;
                ty2

    (* Replaces all resolved TVs with the representative element, if it exists. *)
    let rec resolve_ty =
        let open Type in
        function
            | TVar tv ->
                begin
                    match UnionFind.get (TyVar.point tv) with
                        | Unresolved -> TVar tv
                        | Resolved ty -> ty
                end
            | TFun (t1, t2) -> TFun (resolve_ty t1, resolve_ty t2)
            | ty -> ty

    let typecheck expr =
        let ty = tc StringMap.empty expr in
        Format.printf "Unsolved type: %a\n" Type.pp ty;
        resolve_ty ty
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
        let mk_fun x ann body = EFun (x, ann, body)
        let mk_app e1 e2 = EApp (e1, e2)
        let mk_if cond t e = EIf (cond, t, e)
    end

    let typecheck = Typecheck.typecheck
    let reset_state = Type.TyVar.reset
end
