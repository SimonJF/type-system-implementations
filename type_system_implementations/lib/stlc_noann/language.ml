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

module Solution = struct
    type t = (TyVar.t * Type.t) list
    let of_list x = x
    let as_list x = x

    let rec apply sol : Type.t -> Type.t = function
        | TVar tv ->
              begin
                  match List.assoc_opt tv sol with
                    | Some ty -> ty
                    | None -> TVar tv
              end
        | TFun (t1, t2) -> TFun (apply sol t1, apply sol t2)
        | t -> t

    let pp ppf sol =
        let pp_semi ppf () = Format.pp_print_string ppf "; " in
        let pp_entry ppf (tv, ty) =
            Format.fprintf ppf "%a |-> %a" TyVar.pp tv Type.pp ty
        in
        let sol_list = as_list sol in
        Format.pp_print_list
            ~pp_sep:pp_semi
            pp_entry ppf sol_list

end

module Solver = struct
    open UnionFind
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


    (* Solves a constraint set via unification *)
    let solve : ConstraintSet.t -> Solution.t = fun constrs ->
        let tvs : (TyVar.t, (Type.t ) elem) Hashtbl.t = Hashtbl.create 30 in
    
        (* Assumes TVs has been populated at the end of a unification run. *)
        (* Replaces all resolved TVs with the representative element, if it exists. *)
        let rec resolve_ty =
            let open Type in
            function
                | TVar tv ->
                    begin
                        match Hashtbl.find_opt tvs tv with
                            | Some point -> UnionFind.get point
                            | None -> TVar tv
                    end
                | TFun (t1, t2) -> TFun (resolve_ty t1, resolve_ty t2)
                | ty -> ty
        in
        let rec unify t1 t2 =
            let open Type in
            match t1, t2 with
                 | t1, t2 when t1 = t2 -> ()
                 | TFun (ta1, ta2), TFun (tb1, tb2) ->
                    unify ta1 tb1; unify ta2 tb2
                 | TVar tv, t
                 | t, TVar tv ->
                     occurs_check tv t;
                     begin
                         match Hashtbl.find_opt tvs tv with
                            | Some point -> unify (UnionFind.get point) t
                            | None ->
                                Hashtbl.add tvs tv (UnionFind.make t)
                     end
                | _, _ ->
                    let err =
                        Format.asprintf "Cannot unify %a with %a"
                            Type.pp t1
                            Type.pp t2
                    in
                    raise (Errors.type_error err)
        in
        ConstraintSet.iter (fun (t1, t2) -> unify t1 t2) constrs;
        Hashtbl.to_seq tvs
            |> List.of_seq
            |> List.map (fun (tv, point) -> (tv, resolve_ty (UnionFind.get point)))
            |> Solution.of_list
end


(* TODO: To make this compile when instantiating it in the REPL I think we will
   need Typecheck to be a functor taking an AST as an argument (even though we
   know the exact implementation here).

   In order to allow pattern matching we might be able to do something with the
   'with type' notation.
 *)
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
            let (ty1, constrs1) = tc env e1 in
            let (ty2, constrs2) = tc env e2 in
            match op with
                | And | Or ->
                    let constrs =
                        ConstraintSet.of_list [
                           Constraint.make ty1 Type.TBool;
                           Constraint.make ty2 Type.TBool;
                        ]
                    in
                    (TBool, ConstraintSet.union_many [constrs1; constrs2; constrs])
                (* Polymorphic equality *)
                | Eq | NEq ->
                    let constrs =
                        ConstraintSet.make_singleton ty1 ty2
                    in
                    (TBool, ConstraintSet.union_many [constrs1; constrs2; constrs])
                (* Relational numeric operators *)
                | LT | GT | LEq | GEq ->
                    let constrs =
                        ConstraintSet.of_list [
                           Constraint.make ty1 Type.TInt;
                           Constraint.make ty2 Type.TInt;
                        ]
                    in
                    (TBool, ConstraintSet.union_many [constrs1; constrs2; constrs])
                (* Numeric operators *)
                | Add | Mul | Sub | Div ->
                    let constrs =
                        ConstraintSet.of_list [
                           Constraint.make ty1 Type.TInt;
                           Constraint.make ty2 Type.TInt;
                        ]
                    in
                    (TInt, ConstraintSet.union_many [constrs1; constrs2; constrs])
        in
        function
            | EVar v -> StringMap.find v env, ConstraintSet.empty
            | EFun (bnd, ty_opt, body) ->
                (* If we have a type annotation, use that --
                   otherwise create fresh type variable *)
                let arg_ty =
                    match ty_opt with
                        | Some ann -> ann
                        | None -> TVar (TyVar.fresh ())
                in
                let env' = StringMap.add bnd arg_ty env in
                let (body_ty, body_constrs) = tc env' body in
                TFun (arg_ty, body_ty), body_constrs
            | EApp (e1, e2) ->
                let ftv = TVar (TyVar.fresh ()) in
                let (ty1, constrs1) = tc env e1 in
                let (ty2, constrs2) = tc env e2 in
                let funty_constr =
                    ConstraintSet.make_singleton ty1 (TFun (ty2, ftv))
                in
                ftv, ConstraintSet.union_many [constrs1; constrs2; funty_constr]
            | EBinOp (op, e1, e2) -> tc_binop op e1 e2
            | EConst c -> tc_const c, ConstraintSet.empty
            | ELet (bnd, e1, e2) ->
                let (ty1, constrs1) = tc env e1 in
                let env' = StringMap.add bnd ty1 env in
                let (ty2, constrs2) = tc env' e2 in
                ty2, ConstraintSet.union constrs1 constrs2
            | EAnn (e, ann) ->
                let (ty, constrs1) = tc env e in
                let constrs2 =
                    ConstraintSet.make_singleton ty ann
                in
                ann, ConstraintSet.union constrs1 constrs2
            | EIf (e1, e2, e3) ->
                let (ty1, constrs1) = tc env e1 in
                let (ty2, constrs2) = tc env e2 in
                let (ty3, constrs3) = tc env e3 in
                let new_constrs = ConstraintSet.of_list [
                   Constraint.make ty1 TBool;
                   Constraint.make ty2 ty3
                ]
                in
                let constrs =
                    ConstraintSet.union_many [constrs1; constrs2; constrs3; new_constrs]
                in
                ty2, constrs

    let typecheck expr =
        let (ty, constrs) = tc StringMap.empty expr in
        Format.printf "Unsolved type: %a\n" Type.pp ty;
        Format.printf "Constraint set: %a\n" ConstraintSet.pp constrs;
        let sol = Solver.solve constrs in
        Format.printf "Solution: %a\n" Solution.pp sol;
        Solution.apply sol ty
end

module Language : LANGUAGE = struct
    module TyVar = TyVar
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
        let mk_ann e t = EAnn (e, t)
        let mk_if cond t e = EIf (cond, t, e)
    end

    let typecheck = Typecheck.typecheck
    let reset_state = TyVar.reset
end
