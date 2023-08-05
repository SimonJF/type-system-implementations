open Common_types

module type TYPE = sig
    type t
    val pp : Format.formatter -> t -> unit
end

type binder = string
type variable = string

module type EXPR = sig
    type t
    type binder = string
    type variable = string
end

module type LANGUAGE = sig
    module Type : TYPE
    module Expr : EXPR

    module Type_constructors : sig
        val mk_int : Type.t
        val mk_bool : Type.t
        val mk_string : Type.t
        val mk_unit : Type.t
        val mk_fun : Type.t -> Type.t -> Type.t
    end

    module Expr_constructors : sig
        val mk_constant : Constant.t -> Expr.t
        val mk_variable : variable -> Expr.t
        val mk_let : binder -> Expr.t -> Expr.t -> Expr.t
        val mk_bin_op : BinOp.t -> Expr.t -> Expr.t -> Expr.t
        val mk_fun : binder -> Type.t option -> Expr.t -> Expr.t
        val mk_app : Expr.t -> Expr.t -> Expr.t
        val mk_if : Expr.t -> Expr.t -> Expr.t -> Expr.t
    end

    val typecheck : Expr.t -> Type.t
    val reset_state : unit -> unit
end
