type block = {
  label : string;
  instrs : Tcg.instr list;
  succs : string list;
}

type func = {
  name : string;
  blocks : block list;
}

type program = {
  tcg : Tcg.program;
  funcs : func list;
}

let of_tcg tcg = { tcg; funcs = [] }

