%parameter<Language : Language_sig.LANGUAGE>
%{
  open Hashtbl
  open Common_types
  open Language

  let table = create 1024;;
%}

%start expr_main
%start ty_main
%type <Language.Expr.t> expr_main
%type <Language.Type.t> ty_main

%%

ty:
  | atomic_ty ARROW ty { Language.Type_constructors.mk_fun $1 $3 }
  | atomic_ty { $1 }

/* Atomic types are those that never need extra parentheses */
atomic_ty :
    LPAREN ty RPAREN { $2 }
  | STRING { Type_constructors.mk_string }
  | INT { Type_constructors.mk_int }
  | BOOL { Type_constructors.mk_bool }
  | UNIT { Type_constructors.mk_unit }

/* This is the root of a expr */
expr :
  | LAMBDA ID DOT expr
      { Expr_constructors.mk_fun $2 None $4 }
  | LAMBDA ID COLON ty DOT expr
      { Expr_constructors.mk_fun $2 (Some $4) $6 }
  | LET ID EQ expr IN expr
      { Expr_constructors.mk_let $2 $4 $6 }
  | IF expr THEN expr ELSE expr
      { Expr_constructors.mk_if $2 $4 $6 }
  | fact basic_expr { Expr_constructors.mk_app $1 $2 }
  | LPAREN expr COLON ty RPAREN { Expr_constructors.mk_ann $2 $4 }
  | basic_expr { $1 }

basic_expr :
  | basic_expr AND basic_expr { Expr_constructors.mk_bin_op BinOp.And $1 $3 }
  | basic_expr OR basic_expr { Expr_constructors.mk_bin_op BinOp.Or $1 $3 }
  | basic_expr EQQ basic_expr { Expr_constructors.mk_bin_op BinOp.Eq $1 $3 }
  | basic_expr NEQ basic_expr { Expr_constructors.mk_bin_op BinOp.NEq $1 $3 }
  | basic_expr LT basic_expr { Expr_constructors.mk_bin_op BinOp.LT $1 $3 }
  | basic_expr GT basic_expr { Expr_constructors.mk_bin_op BinOp.GT $1 $3 }
  | basic_expr LEQ basic_expr { Expr_constructors.mk_bin_op BinOp.LEq $1 $3 }
  | basic_expr GEQ basic_expr { Expr_constructors.mk_bin_op BinOp.GEq $1 $3 }
  | basic_expr PLUS basic_expr { Expr_constructors.mk_bin_op BinOp.Add $1 $3 }
  | basic_expr MINUS basic_expr { Expr_constructors.mk_bin_op BinOp.Sub $1 $3 }
  | basic_expr STAR basic_expr { Expr_constructors.mk_bin_op BinOp.Mul $1 $3 }
  | basic_expr DIV basic_expr { Expr_constructors.mk_bin_op BinOp.Div $1 $3 }
  | fact { $1 }


fact :
    LPAREN expr RPAREN { $2 }
  | ID { try find table $1 with Not_found -> Expr_constructors.mk_variable ($1) }
  | STRINGV { Expr_constructors.mk_constant (Constant.CString $1) }
  | INTV { Expr_constructors.mk_constant (Constant.CInt $1) }
  | TRUE { Expr_constructors.mk_constant (Constant.CBool true) }
  | FALSE { Expr_constructors.mk_constant (Constant.CBool false) }
  | UNITV { Expr_constructors.mk_constant Constant.CUnit }

expr_main:
    | expr EOF { $1 }
ty_main:
    | ty EOF { $1 }

