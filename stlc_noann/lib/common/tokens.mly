/* Tokens */
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

%token <string> ID
%token <string> STRINGV
%token <int> INTV

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

%%
