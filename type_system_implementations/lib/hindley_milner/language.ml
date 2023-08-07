(* Hindley-Milner: Implementation of Algorithm J for Hindley-Milner type inference *)
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
    module StringSet = Set.Make(String)
    exception Occurs_check

    let rec ftvs =
        let open Type in
        function
            | TVar tv -> StringSet.singleton (TyVar.var tv)
            | TFun (t1, t2) ->
                StringSet.union (ftvs t1) (ftvs t2)
            | TPair (t1, t2) ->
                StringSet.union (ftvs t1) (ftvs t2)
            | _ -> StringSet.empty

    let ftvs_mono = ftvs

    let ftvs_poly (quants, mono) =
        let mono_vars = ftvs mono in
        StringSet.diff mono_vars quants

    (* In order to avoid unnecessary computation in generalisation,
       record FTVs along with the environment itself *)
    module Env = struct
        (* Type environments actually map variables to polytypes, even though
           typechecking only ever returns a monotype *)
        type t = StringSet.t * (Type.polytype StringMap.t)

        let empty = (StringSet.empty, StringMap.empty)

        let ftvs = fst

        let bind_poly k (quants, ty) (env_ftvs, env) : t =
            let ty_ftvs = StringSet.diff (ftvs_mono ty) (StringSet.of_list quants) in
            (StringSet.union env_ftvs ty_ftvs,
             StringMap.add k (quants, ty) env)
        
        let bind (k: Expr.variable) (ty: Type.monotype) : t -> t =
            bind_poly k ([], ty)

        let find k (_, env) =
            match StringMap.find_opt k env with
                | Some ty -> ty
                | None -> raise (Errors.type_error ("Unbound variable " ^ k))
    end
    type env = Env.t

    (* HM instantiation: substitute fresh TVs for all quantifiers *)
    let instantiate (poly : Type.polytype) : Type.monotype =
        let open Type in
        let (quants, mono) = poly in
        (* For each quantifier, create a fresh type variable *)
        let subst_map =
            List.map (fun q -> (q, TyVar.fresh ())) quants
        in
        (* Substitute the quantified TV for the fresh TV *)
        let rec go = function
            | TVar tv ->
                begin
                    match List.assoc_opt (TyVar.var tv) subst_map with
                        | Some inst -> TVar inst
                        | None -> TVar tv
                end
            | TFun (t1, t2) -> TFun (go t1, go t2)
            | TPair (t1, t2) -> TPair (go t1, go t2)
            | t -> t
        in
        go mono

    (* HM generalisation: Generate type scheme for monotype, quantifying all
       FTVs in the type that do not already occur in the environment. *)
    let generalise env (monotype: Type.monotype) : Type.polytype =
        (* Calculate FTVs in type *)
        let type_ftvs = StringSet.diff (ftvs monotype) (Env.ftvs env) in
        (* Host to quantifiers *)
        (List.map Type.Quantifier.make (StringSet.elements type_ftvs)), monotype

    (* Checks whether type variable tv occurs in type t *)
    let occurs_check tv ty =
        let open Type in
        let rec go =
            function
                | TVar tv' ->
                    if tv = tv' then
                        raise Occurs_check
                | TFun  (t1, t2)
                | TPair (t1, t2) -> go t1; go t2
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

    let rec is_value =
        let open Expr in
        function
            | EPair (e1, e2) -> is_value e1 && is_value e2
            | EAnn (e, _) -> is_value e
            | EVar _ | EConst _ | EFun _ -> true
            | _ -> false

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
    let rec tc (env: Env.t) =
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
            | EVar v -> instantiate (Env.find v env)
            | EFun (bnd, ty_opt, body) ->
                (* If we have a type annotation, use that --
                   otherwise create fresh type variable *)
                let arg_ty =
                    match ty_opt with
                        | Some ann -> ann
                        | None -> Type.fresh_var ()
                in
                let env' = Env.bind bnd arg_ty env in
                let body_ty = tc env' body in
                TFun (arg_ty, body_ty)
            | EApp (e1, e2) ->
                let ftv = Type.fresh_var () in
                let ty1 = tc env e1 in
                let ty2 = tc env e2 in
                unify ty1 (TFun (ty2, ftv));
                ftv
            | EBinOp (op, e1, e2) -> tc_binop op e1 e2
            | EConst c -> tc_const c
            | ELet (bnd, e1, e2) ->
                (* Check whether we can generalise e1 (i.e., is it a syntactic value?).
                   This is due to the value restriction. *)
                let ty1 = tc env e1 in
                let env' =
                    if is_value e1 then
                        (* Generalise *)
                        Env.bind_poly bnd (generalise env ty1) env
                    else
                        Env.bind bnd ty1 env
                in
                let ty2 = tc env' e2 in
                ty2
            | ELetPair (x, y, e1, e2) ->
                let ty1 = tc env e1 in
                let var1 = Type.fresh_var () in
                let var2 = Type.fresh_var () in
                unify (TPair (var1, var2)) ty1;
                let env = Env.bind x var1 env in
                let env = Env.bind y var2 env in
                let ty2 = tc env e2 in
                ty2
            | EPair (e1, e2) ->
                let ty1 = tc env e1 in
                let ty2 = tc env e2 in
                TPair (ty1, ty2)
            | EFst e ->
                let ty = tc env e in
                TPair (ty, Type.fresh_var ())
            | ESnd e ->
                let ty = tc env e in
                TPair (Type.fresh_var (), ty)
            | EAnn (e, ann) ->
                let ty = tc env e in
                unify ty ann;
                ann
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
            | TPair (t1, t2) -> TPair (resolve_ty t1, resolve_ty t2)
            | ty -> ty

    let typecheck expr =
        let ty = tc Env.empty expr in
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
