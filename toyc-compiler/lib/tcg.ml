type value =
  | Temp of int
  | Imm of int64

type instr =
  | Label of string
  | Move of value * value
  | Comment of string

type func = {
  name : string;
  body : instr list;
}

type program = {
  ast : Ast.program;
  funcs : func list;
}

let of_ast ast = { ast; funcs = [] }
