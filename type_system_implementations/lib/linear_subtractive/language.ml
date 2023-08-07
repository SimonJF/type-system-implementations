(* linear_subtractive: Based on stlc_noann_onthefly.
   Implements a subtractive checker for linear types (similar to the one in ATAPL).
   A variable is deleted from an environment as soon as it is used. *)
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
             | TFun (ta1, ta2), TFun (tb1, tb2)
             | TPair (ta1, ta2), TPair (tb1, tb2) ->
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
            let (ty1, env) = tc env e1 in
            let (ty2, env) = tc env e2 in
            match op with
                | And | Or ->
                    unify ty1 Type.TBool;
                    unify ty2 Type.TBool;
                    TBool, env
                (* Polymorphic equality *)
                | Eq | NEq ->
                    unify ty1 ty2;
                    TBool, env
                (* Relational numeric operators *)
                | LT | GT | LEq | GEq ->
                    unify ty1 Type.TInt;
                    unify ty2 Type.TInt;
                    TBool, env
                (* Numeric operators *)
                | Add | Mul | Sub | Div ->
                    unify ty1 Type.TInt;
                    unify ty2 Type.TInt;
                    TInt, env
        in
        let check_variable_used v env =
            if StringMap.mem v env then
                raise (Errors.type_error (Format.asprintf "Linear variable %s unused" v))
        in
        function
            | EVar v ->
                let ty =
                    match StringMap.find_opt v env with
                        | Some ty -> ty
                        | None ->
                            raise (Errors.type_error (Format.asprintf "Variable %s not found. Perhaps it has been used already?" v))
                in
                    (ty, StringMap.remove v env)
            | EFun (bnd, ty_opt, body) ->
                (* If we have a type annotation, use that --
                   otherwise create fresh type variable *)
                let arg_ty =
                    match ty_opt with
                        | Some ann -> ann
                        | None -> TVar (TyVar.fresh ())
                in
                let env = StringMap.add bnd arg_ty env in
                let body_ty, env = tc env body in
                check_variable_used bnd env;
                TFun (arg_ty, body_ty), env
            | EApp (e1, e2) ->
                let ftv = TVar (TyVar.fresh ()) in
                let ty1, env = tc env e1 in
                let ty2, env = tc env e2 in
                unify ty1 (TFun (ty2, ftv));
                ftv, env
            | EBinOp (op, e1, e2) -> tc_binop op e1 e2
            | EConst c -> tc_const c, env
            | ELet (bnd, e1, e2) ->
                let ty1, env = tc env e1 in
                let env = StringMap.add bnd ty1 env in
                let ty2, env = tc env e2 in
                check_variable_used bnd env;
                ty2, env
            | EAnn (e, ann) ->
                let ty, env = tc env e in
                unify ty ann;
                ann, env
            | EIf (e1, e2, e3) ->
                let ty1, env = tc env e1 in
                let ty2, env1 = tc env e2 in
                let ty3, env2 = tc env e3 in
                (* Ensure that env1 and env2 are consistent *)
                (* Slight misuse of 'merge' for the side-effects,
                   but it's a cool function. *)
                let _ =
                    StringMap.merge (fun k ty1_opt ty2_opt ->
                        match ty1_opt, ty2_opt with
                            | Some ty1, Some ty2 -> unify ty1 ty2; None
                            | _, _ ->
                                raise (Errors.type_error (
                                    Format.asprintf "Variable %s not used consistently across branches" k))
                    ) env1 env2
                in
                unify ty1 TBool;
                unify ty2 ty3;
                ty2, env1
            | ELetPair (x, y, e1, e2) ->
                let ty1, env = tc env e1 in
                let var1 = Type.fresh_var () in
                let var2 = Type.fresh_var () in
                unify (TPair (var1, var2)) ty1;
                let env = StringMap.add x var1 env in
                let env = StringMap.add y var2 env in
                let ty2, env = tc env e2 in
                check_variable_used x env;
                check_variable_used y env;
                ty2, env
            | EPair (e1, e2) ->
                let ty1, env = tc env e1 in
                let ty2, env = tc env e2 in
                TPair (ty1, ty2), env
            | EFst e ->
                let ty, env = tc env e in
                TPair (ty, Type.fresh_var ()), env
            | ESnd e ->
                let ty, env = tc env e in
                TPair (Type.fresh_var (), ty), env
            
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
        let ty, env = tc StringMap.empty expr in
        assert (StringMap.is_empty env);
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
        let mk_pair t1 t2 = TPair (t1, t2)
    end

    module Expr_constructors = struct
        open Expr
        let mk_constant c = EConst c
        let mk_variable v = EVar v
        let mk_let x e1 e2 = ELet (x, e1, e2)
        let mk_bin_op op e1 e2 = EBinOp (op, e1, e2)
        let mk_fun x ann body = EFun (x, ann, body)
        let mk_app e1 e2 = EApp (e1, e2)
        let mk_ann e t = EAnn (e, t)
        let mk_if cond t e = EIf (cond, t, e)
        let mk_letpair x y e1 e2 = ELetPair (x, y, e1, e2)
        let mk_pair e1 e2 = EPair (e1, e2)
        let mk_fst e = EFst e
        let mk_snd e = ESnd e
    end

    let typecheck = Typecheck.typecheck
    let reset_state = Type.TyVar.reset
end
