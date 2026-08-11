type loc = {
  line : int;
  col : int;
}

type ident = {
  name : string;
  id : int;
  loc : loc;
}

type typ =
  | TInt
  | TVoid

type unop =
  | UPlus
  | UMinus
  | UNot

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Lt
  | Gt
  | Le
  | Ge
  | Eq
  | Ne
  | LAnd
  | LOr

type expr =
  | Int of int64
  | Var of string
  | Call of string * expr list
  | Unary of unop * expr
  | Binary of binop * expr * expr

type decl = {
  is_const : bool;
  ident : ident;
  init : expr;
}

type stmt =
  | Block of stmt list
  | Empty
  | Expr of expr
  | Assign of string * expr
  | Decl of decl
  | If of expr * stmt * stmt option
  | While of expr * stmt
  | Break
  | Continue
  | Return of expr option

type func = {
  ret : typ;
  name : ident;
  params : ident list;
  body : stmt list;
}

type top =
  | TopDecl of decl
  | FuncDef of func

type program = top list

