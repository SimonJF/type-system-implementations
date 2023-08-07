open Common.Common_types

(* Main difference here is that type variables also contain a union-find point. *)
module Type = struct

    module Quantifier = struct
        type t = string
        let make x = x
        let of_tyvar (tv, _) = tv
        let pp = Format.pp_print_string
        let compare = String.compare
    end

    type quantifier = Quantifier.t
    type resolution_state =  Unresolved | Resolved of t
    and tyvar = string * (resolution_state UnionFind.elem)
    and monotype =
        | TVar of tyvar
        | TInt
        | TBool
        | TString
        | TUnit
        | TFun of (t * t)
        | TPair of (t * t)
    and polytype = quantifier list * monotype
    and t = monotype
        
    module TyVar = struct
        let source = ref 0
        let reset () = source := 0

        let fresh ?(prefix="_") () =
            let sym = !source in
            let () = incr source in
            let point = UnionFind.make Unresolved in
            prefix ^ (string_of_int sym), point

        let pp ppf (tv, _) = Format.pp_print_string ppf tv
        let var = fst
        let point = snd
        let compare (tv1, _) (tv2, _) = String.compare tv1 tv2
    end

    let fresh_var () = TVar (TyVar.fresh ())

    let rec pp_monotype ppf =
        let open Format in
        function
            | TVar tv -> TyVar.pp ppf tv
            | TInt -> pp_print_string ppf "Int"
            | TBool -> pp_print_string ppf "Bool"
            | TString -> pp_print_string ppf "String"
            | TUnit -> pp_print_string ppf "Unit"
            | TFun (t1, t2) -> fprintf ppf "(%a -> %a)" pp_monotype t1 pp_monotype t2
            | TPair (t1, t2) -> fprintf ppf "(%a * %a)" pp_monotype t1 pp_monotype t2

    let pp_polytype ppf (quants, mono) =
        let open Format in
        (* Only print quantifiers if we have some! *)
        if quants = [] then
            pp_monotype ppf mono
        else
            let pp_space ppf () = pp_print_string ppf " " in
            let print_quants ppf quants =
                pp_print_list ~pp_sep:(pp_space) Quantifier.pp ppf quants
            in
            Format.fprintf ppf "forall %a. %a" print_quants quants pp_monotype mono

    let pp = pp_monotype

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
        | EAnn of (t * ty)
        | EIf of (t * t * t)
        | EPair of (t * t)
        | ELetPair of (variable * variable * t * t)
        | EFst of t
        | ESnd of t
end
