%{
  open Hashtbl
  open Ast

  let table = create 1024;;
  let binary_op op e1 e2 = Expr.EBinOp (op, e1, e2)
%}

/* Keyword tokens */
%token LAMBDA
%token LET
%token IN
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token STRING
%token INT
%token BOOL
%token UNIT
%token UNITV

/* Identifiers tokens */
%token <string> ID
%token <string> STRINGV
%token <int> INTV

/* Symbolic tokens */
%token LPAREN
%token RPAREN
%token DOT
%token EQ
%token ARROW
%token EOF
%token AND OR
%token LT GT GEQ LEQ EQQ NEQ
%token PLUS MINUS
%token STAR DIV

/* Precedence */
%left AND OR
%left LT GT GEQ LEQ EQQ NEQ
%left PLUS MINUS
%left STAR DIV

%start expr_main
%start ty_main
%type <Ast.Expr.t> expr_main
%type <Ast.Type.t> ty_main

%%

ty:
  | atomic_ty ARROW ty
      { TFun ($1, $3) }
  | atomic_ty { $1 }

/* Atomic types are those that never need extra parentheses */
atomic_ty :
    LPAREN ty RPAREN { $2 }
  | STRING { Type.TString }
  | INT { Type.TInt }
  | BOOL { Type.TBool }
  | UNIT { Type.TUnit }

/* This is the root of a expr */
expr :
  | LAMBDA ID DOT expr
      { Expr.EFun ($2, $4) }
  | LET ID EQ expr IN expr
      { Expr.ELet ($2, $4, $6) }
  | IF expr THEN expr ELSE expr
      { Expr.EIf ($2, $4, $6) }
  | fact basic_expr { Expr.EApp ($1, $2) }
  | basic_expr { $1 }

basic_expr :
  | basic_expr AND basic_expr { binary_op BinOp.And $1 $3 }
  | basic_expr OR basic_expr { binary_op BinOp.Or $1 $3 }
  | basic_expr EQQ basic_expr { binary_op BinOp.Eq $1 $3 }
  | basic_expr NEQ basic_expr { binary_op BinOp.NEq $1 $3 }
  | basic_expr LT basic_expr { binary_op BinOp.LT $1 $3 }
  | basic_expr GT basic_expr { binary_op BinOp.GT $1 $3 }
  | basic_expr LEQ basic_expr { binary_op BinOp.LEq $1 $3 }
  | basic_expr GEQ basic_expr { binary_op BinOp.GEq $1 $3 }
  | basic_expr PLUS basic_expr { binary_op BinOp.Add $1 $3 }
  | basic_expr MINUS basic_expr { binary_op BinOp.Sub $1 $3 }
  | basic_expr STAR basic_expr { binary_op BinOp.Mul $1 $3 }
  | basic_expr DIV basic_expr { binary_op BinOp.Div $1 $3 }
  | fact { $1 }


fact :
    LPAREN expr RPAREN { $2 }
  | ID { try find table $1 with Not_found -> Expr.EVar ($1) }
  | STRINGV { Expr.EConst (Constant.CString $1) }
  | INTV { Expr.EConst (Constant.CInt $1) }
  | TRUE { Expr.EConst (Constant.CBool true) }
  | FALSE { Expr.EConst (Constant.CBool false) }
  | UNITV { Expr.EConst Constant.CUnit }

expr_main:
    | expr EOF { $1 }
ty_main:
    | ty EOF { $1 }

