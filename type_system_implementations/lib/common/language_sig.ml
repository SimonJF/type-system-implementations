open Common_types

module type TYPE = sig
    type t
    val mk_int : t
    val mk_bool : t
    val mk_string : t
    val mk_unit : t
    val mk_fun : t -> t -> t
    val pp : Format.formatter -> t -> unit
end

type binder = string
type variable = string

module type EXPR = sig
    type t
    type ty
    type binder = string
    type variable = string
    val mk_constant : Constant.t -> t
    val mk_variable : variable -> t
    val mk_let : binder -> t -> t -> t
    val mk_bin_op : BinOp.t -> t -> t -> t
    val mk_fun : binder -> ty option -> t -> t
    val mk_app : t -> t -> t
    val mk_if : t -> t -> t -> t
end

module type LANGUAGE = sig
    module Type : TYPE
    module Expr : EXPR

    val typecheck : Expr.t -> Type.t
    val reset_state : unit -> unit
end
