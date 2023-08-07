(* Co-contextual type system: produces a type environment as an *output* rather than an input.
   Lends itself almost immediately to implementing a linear type system. *)
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
        | TPair (t1, t2) -> TPair (apply sol t1, apply sol t2)
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
                 | TFun (ta1, ta2), TFun (tb1, tb2)
                 | TPair (ta1, ta2), TPair (tb1, tb2) ->
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

    let check_env x ty env =
        match StringMap.find_opt x env with
            | Some env_ty -> ConstraintSet.make_singleton ty env_ty
            | None ->
                (* NOTE: For a linear variant, need to raise an error here *)
                ConstraintSet.empty

    let merge_unrestricted env1 env2 =
       (* Find overlapping entries *)
       let overlapping_keys =
           StringMap.bindings env1
           |> List.filter_map
                (fun (k, _) -> if StringMap.mem k env2 then Some k else None)
       in
       (* Create constraints for overlapping variables *)
       let constrs =
           List.map (fun k ->
               Constraint.make (StringMap.find k env1) (StringMap.find k env2))
               overlapping_keys
           |> ConstraintSet.of_list
       in
       (* For non-overlapping, simply union environments *)
       let env =
           StringMap.merge (fun _ ty1_opt ty2_opt ->
               match ty1_opt, ty2_opt with
                 (* Note: in Some,Some case, constraint already made *)
                 | Some ty, _ | _, Some ty -> Some ty
                 | None, None -> None
           ) env1 env2
       in
       env, constrs

    (* Typechecking: constructs a type, an environment, and a constraint set *)
    (* Takes merge: env -> env -> (env * constrs) as an argument *)
    let typecheck_expr merge e =
        let merge_many =
            List.fold_left
                (fun (acc, constrs) env ->
                    let (acc', merge_constrs) = merge acc env in
                    (acc', ConstraintSet.union constrs merge_constrs))
                (StringMap.empty, ConstraintSet.empty)
        in
        let rec tc =
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
                let (ty1, env1, constrs1) = tc e1 in
                let (ty2, env2, constrs2) = tc e2 in
                let (env, env_constrs) = merge env1 env2 in
                match op with
                    | And | Or ->
                        let constrs =
                            ConstraintSet.of_list [
                               Constraint.make ty1 Type.TBool;
                               Constraint.make ty2 Type.TBool;
                            ]
                        in
                        (TBool, env, ConstraintSet.union_many [constrs1; constrs2; constrs; env_constrs])
                    (* Polymorphic equality *)
                    | Eq | NEq ->
                        let constrs =
                            ConstraintSet.make_singleton ty1 ty2
                        in
                        (TBool, env, ConstraintSet.union_many [constrs1; constrs2; env_constrs; constrs])
                    (* Relational numeric operators *)
                    | LT | GT | LEq | GEq ->
                        let constrs =
                            ConstraintSet.of_list [
                               Constraint.make ty1 Type.TInt;
                               Constraint.make ty2 Type.TInt;
                            ]
                        in
                        (TBool, env, ConstraintSet.union_many [constrs1; constrs2; env_constrs; constrs])
                    (* Numeric operators *)
                    | Add | Mul | Sub | Div ->
                        let constrs =
                            ConstraintSet.of_list [
                               Constraint.make ty1 Type.TInt;
                               Constraint.make ty2 Type.TInt;
                            ]
                        in
                        (TInt, env, ConstraintSet.union_many [constrs1; constrs2; env_constrs; constrs])
            in
            function
                | EVar v ->
                    (* We don't have an environment to look things up in, so need to create a fresh TV 
                       and constrain on our way down the tree. *)
                    let tv = Type.fresh_var () in
                    let env = StringMap.singleton v tv in
                    tv, env, ConstraintSet.empty
                | EFun (bnd, ty_opt, body) ->
                    (* Typecheck the body to get env *)
                    let (body_ty, env, body_constrs) = tc body in
                    (* If we have an annotation and use the variable in the body, we need to
                       generate a constraint *)
                    let arg_ty = Type.fresh_var () in
                    let arg_constrs =
                        match StringMap.find_opt bnd env with
                            | Some ty -> ConstraintSet.make_singleton arg_ty ty
                            | None -> ConstraintSet.empty
                    in
                    let ann_constrs =
                        match ty_opt, StringMap.find_opt bnd env with
                            | Some ann, Some inferred ->
                                    ConstraintSet.make_singleton inferred ann
                            | _, _ -> ConstraintSet.empty
                    in
                    let constrs =
                        ConstraintSet.union_many [
                            body_constrs;
                            arg_constrs;
                            ann_constrs
                        ]
                    in
                    (* Remove bound variable from environment *)
                    let env = StringMap.remove bnd env in
                    TFun (arg_ty, body_ty), env, constrs
                | EApp (e1, e2) ->
                    let ftv = TVar (TyVar.fresh ()) in
                    let (ty1, env1, constrs1) = tc e1 in
                    let (ty2, env2, constrs2) = tc e2 in
                    let funty_constr =
                        ConstraintSet.make_singleton ty1 (TFun (ty2, ftv))
                    in
                    let env, env_constrs = merge env1 env2 in
                    ftv, env, ConstraintSet.union_many [constrs1; constrs2; funty_constr; env_constrs]
                | EBinOp (op, e1, e2) -> tc_binop op e1 e2
                | EConst c -> tc_const c, StringMap.empty, ConstraintSet.empty
                | ELet (bnd, e1, e2) ->
                    (* Typecheck e1 and e2; if x is in env2 then ensure it has same type as ty1 *)
                    let (ty1, env1, constrs1) = tc e1 in
                    let (ty2, env2, constrs2) = tc e2 in

                    let check_env_constrs = check_env bnd ty1 env2 in 
                    let env, env_constrs = merge env1 (StringMap.remove bnd env2) in
                    let constrs = ConstraintSet.union_many [
                        constrs1; constrs2; check_env_constrs; env_constrs]
                    in
                    ty2, env, constrs
                | EAnn (e, ann) ->
                    let (ty, env, constrs1) = tc e in
                    let constrs2 =
                        ConstraintSet.make_singleton ty ann
                    in
                    ann, env, ConstraintSet.union constrs1 constrs2
                | EIf (e1, e2, e3) ->
                    let (ty1, env1, constrs1) = tc e1 in
                    let (ty2, env2, constrs2) = tc e2 in
                    let (ty3, env3, constrs3) = tc e3 in
                    let new_constrs = ConstraintSet.of_list [
                       Constraint.make ty1 TBool;
                       Constraint.make ty2 ty3
                    ]
                    in
                    (* Note: We need to do something a bit more sophisticated to
                       lift this to linear type systems since we'll be wanting
                       to ensure consistent variable use across the two
                       branches, and then do the usual join with the conditional *)
                    let (env, env_constrs) = merge_many [env1; env2; env3] in
                    let constrs =
                        ConstraintSet.union_many
                            [constrs1; constrs2; constrs3; env_constrs; new_constrs]
                    in
                    ty2, env, constrs
                | ELetPair (x, y, e1, e2) ->
                    let (ty1, env1, constrs1) = tc e1 in
                    let var1 = Type.fresh_var () in
                    let var2 = Type.fresh_var () in
                    let pair_constrs =
                        ConstraintSet.make_singleton (TPair (var1, var2)) ty1
                    in
                    let (ty2, env2, constrs2) = tc e2 in
                    let (env, env_constrs) = merge env1 env2 in 
                    let check_x_constrs = check_env x var1 env2 in
                    let check_y_constrs = check_env y var2 env2 in
                    let constrs =
                        ConstraintSet.union_many
                            [constrs1; constrs2; pair_constrs; env_constrs;
                             check_x_constrs; check_y_constrs]
                    in
                    let env =
                        env
                        |> StringMap.remove x
                        |> StringMap.remove y
                    in
                    ty2, env, constrs
                | EPair (e1, e2) ->
                    let (ty1, env1, constrs1) = tc e1 in
                    let (ty2, env2, constrs2) = tc e2 in
                    let (env, env_constrs) = merge env1 env2 in
                    TPair (ty1, ty2), env, ConstraintSet.union_many [constrs1; constrs2; env_constrs]
                | EFst e ->
                    let (ty, env, constrs) = tc e in
                    TPair (ty, Type.fresh_var ()), env, constrs
                | ESnd e ->
                    let (ty, env, constrs) = tc e in
                    TPair (Type.fresh_var (), ty), env, constrs
        in tc e
            
    let typecheck expr =
        let (ty, env, constrs) = typecheck_expr merge_unrestricted expr in
        Format.printf "Unsolved type: %a\n" Type.pp ty;
        Format.printf "Constraint set: %a\n" ConstraintSet.pp constrs;
        let sol = Solver.solve constrs in
        Format.printf "Solution: %a\n" Solution.pp sol;
        let solved_env =
            env
            |> StringMap.bindings
            |> List.map (fun (x, ty) -> (x, Solution.apply sol ty))
        in

        let pp_env ppf env =
            let pp_comma ppf () = Format.pp_print_string ppf ", " in
            let pp_entry ppf (x, ty) =
                Format.fprintf ppf "%s: %a" x Type.pp ty
            in
            Format.pp_print_list
                ~pp_sep:pp_comma
                pp_entry ppf env
        in
        Format.printf "Solved environment: %a\n" pp_env solved_env;
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
    let reset_state = TyVar.reset
end
