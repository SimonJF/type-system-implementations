module TyVar = struct
    type t = string
    
    let fresh ?(prefix="_") =
        let source = ref 0 in
        fun () ->
            let sym = !source in
            let () = incr source in
            prefix ^ (string_of_int sym)

    let pp = Format.pp_print_string
end
module Type = struct
    type t =
        | TVar of TyVar.t
        | TNat
        | TBool
        | TFun of (t * t)


    let rec pp ppf =
        function
            | TVar tv -> TyVar.pp ppf tv
            | TNat -> Format.pp_print_string ppf "Nat"
            | TBool -> Format.pp_print_string ppf "Bool"
            | TFun (t1, t2) -> Format.fprintf ppf "%a -> %a" pp t1 pp t2
end

module Expr = struct
    type binder = string
    type variable = string

    type t =
        | EVar of variable
        | EFun of (binder * t)
        | EApp of (t * t)
        | EBool of bool
        | EIf of (t * t * t)
        | EZero
        | EPred of t
        | ESucc of t
        | EIsZero of t
end

module Constraint = struct
    type t = Type.t * Type.t

    let make t1 t2 = (t1, t2)
    let compare = Stdlib.compare
end

module ConstraintSet = struct
    include Set.Make(Constraint)
    let union_many = List.fold_left (union) empty
    let make_singleton t1 t2 = singleton (Constraint.make t1 t2)
end

module Typecheck = struct
    module StringMap = Map.Make(String)

    type env = Type.t StringMap.t

    (* Typechecking: constructs a type and constraint set *)
    let rec tc env =
        let open Expr in
        let open Type in
        function
            | EVar v -> StringMap.find v env, ConstraintSet.empty
            | EFun (bnd, body) ->
                let ftv = TVar (TyVar.fresh ()) in
                let env' = StringMap.add bnd ftv env in
                let (body_ty, body_constrs) = tc env' body in
                TFun (ftv, body_ty), body_constrs
            | EApp (e1, e2) ->
                let ftv = TVar (TyVar.fresh ()) in
                let (ty1, constrs1) = tc env e1 in
                let (ty2, constrs2) = tc env e2 in
                let funty_constr =
                    ConstraintSet.make_singleton ty1 (TFun (ty2, ftv))
                in
                (ftv, ConstraintSet.union_many [constrs1; constrs2; funty_constr])
            | EBool _ -> TBool, ConstraintSet.empty
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
                (ty2, constrs)
            | EZero -> (TNat, ConstraintSet.empty)
            | EPred e
            | ESucc e ->
                let (ty, constrs) = tc env e in
                (ty, ConstraintSet.union constrs (ConstraintSet.make_singleton ty TNat))
            | EIsZero e ->
                let (ty, constrs) = tc env e in
                (TBool, ConstraintSet.union constrs (ConstraintSet.make_singleton ty TNat))


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
        | TNat -> TNat
        | TBool -> TBool
        | TFun (t1, t2) -> TFun (apply sol t1, apply sol t2)

end

module Solve = struct
    open UnionFind
    (* Solves a constraint set via unification *)
    let solve : ConstraintSet.t -> Solution.t = fun constrs ->
        let tvs : (TyVar.t, Type.t elem) Hashtbl.t = Hashtbl.create 30 in
        let rec unify t1 t2 =
            let open Type in
            match (t1, t2) with
                 | t1, t2 when t1 = t2 -> ()
                 | TVar tv, t
                 | t, TVar tv ->
                     begin
                         match Hashtbl.find_opt tvs tv with
                            | Some point ->
                                UnionFind.set point t
                            | None -> Hashtbl.add tvs tv (UnionFind.make t)
                     end
                | TFun (ta1, ta2), TFun (tb1, tb2) ->
                    unify ta1 tb1; unify ta2 tb2
                | _, _ -> failwith "unification failure"
        in
        ConstraintSet.iter (fun (t1, t2) -> unify t1 t2) constrs;
        Hashtbl.to_seq tvs
            |> List.of_seq
            |> List.map (fun (tv, point) -> (tv, UnionFind.get point))
            |> Solution.of_list
end

let () = print_endline "Hello, World!"
