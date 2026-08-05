open Ast

exception Error of string

module StringMap = Map.Make (String)

type temp = int
type label = string

type place =
  | Local of int
  | Global of string

type operand =
  | Temp of temp
  | Imm of int64

type simple_instr =
  | Move of temp * operand
  | Un of temp * unop * operand
  | Bin of temp * binop * operand * operand
  | Load of temp * place
  | Store of place * operand
  | Call of temp option * string * operand list

type instr =
  | Label of label
  | Op of simple_instr
  | Goto of label
  | IfZero of operand * label
  | IfNonZero of operand * label
  | Return of operand option

type var = {
  id : int;
  name : string;
}

type func = {
  ret : typ;
  name : string;
  label : string;
  entry : label;
  params : var list;
  locals : var list;
  temp_count : int;
  body : instr list;
}

type program = {
  funcs : func list;
}

type env = {
  funcs : Semant.func_sig StringMap.t;
  mutable scopes : place StringMap.t list;
  mutable break_labels : label list;
  mutable continue_labels : label list;
}

type builder = {
  func_label : string;
  mutable next_temp : int;
  mutable next_label : int;
  mutable instrs_rev : instr list;
  mutable locals_rev : var list;
}

let err msg = raise (Error msg)

let fresh_temp builder =
  let t = builder.next_temp in
  builder.next_temp <- builder.next_temp + 1;
  t

let fresh_label builder prefix =
  let id = builder.next_label in
  builder.next_label <- builder.next_label + 1;
  Printf.sprintf ".L%s_%s_%d" builder.func_label prefix id

let emit builder instr = builder.instrs_rev <- instr :: builder.instrs_rev

let push_scope env = env.scopes <- StringMap.empty :: env.scopes

let pop_scope env =
  match env.scopes with
  | _ :: rest -> env.scopes <- rest
  | [] -> err "internal empty lowering scope stack"

let add_local env builder (ident : Ast.ident) =
  match env.scopes with
  | scope :: rest ->
      env.scopes <- StringMap.add ident.name (Local ident.id) scope :: rest;
      builder.locals_rev <- { id = ident.id; name = ident.name } :: builder.locals_rev
  | [] -> err "internal empty lowering scope stack"

let lookup_name env name =
  let rec loop = function
    | [] -> None
    | scope :: rest -> (
        match StringMap.find_opt name scope with
        | Some binding -> Some binding
        | None -> loop rest)
  in
  match loop env.scopes with
  | Some binding -> binding
  | None -> err ("internal lowering unknown identifier: " ^ name)

let lookup_func env name =
  match StringMap.find_opt name env.funcs with
  | Some sig_ -> sig_
  | None -> err ("internal lowering unknown function: " ^ name)

let emit_op builder op = emit builder (Op op)

let rec lower_expr env builder = function
  | Int n -> Imm n
  | Var name ->
      let dst = fresh_temp builder in
      emit_op builder (Load (dst, lookup_name env name));
      Temp dst
  | Unary (UPlus, e) -> lower_expr env builder e
  | Unary (op, e) ->
      let src = lower_expr env builder e in
      let dst = fresh_temp builder in
      emit_op builder (Un (dst, op, src));
      Temp dst
  | Binary (LAnd, _, _) as e -> lower_bool_expr env builder e
  | Binary (LOr, _, _) as e -> lower_bool_expr env builder e
  | Binary (op, a, b) ->
      let lhs = lower_expr env builder a in
      let rhs = lower_expr env builder b in
      let dst = fresh_temp builder in
      emit_op builder (Bin (dst, op, lhs, rhs));
      Temp dst
  | Call (name, args) ->
      let sig_ = lookup_func env name in
      let lowered_args = List.map (lower_expr env builder) args in
      (match sig_.ret with
      | TVoid -> err ("internal lowering void call used as value: " ^ name)
      | TInt ->
          let dst = fresh_temp builder in
          emit_op builder (Call (Some dst, sig_.label, lowered_args));
          Temp dst)

and lower_bool_expr env builder e =
  let dst = fresh_temp builder in
  let true_l = fresh_label builder "bool_true" in
  let false_l = fresh_label builder "bool_false" in
  let end_l = fresh_label builder "bool_end" in
  lower_cond env builder e true_l false_l;
  emit builder (Label true_l);
  emit_op builder (Move (dst, Imm 1L));
  emit builder (Goto end_l);
  emit builder (Label false_l);
  emit_op builder (Move (dst, Imm 0L));
  emit builder (Goto end_l);
  emit builder (Label end_l);
  Temp dst

and lower_cond env builder e true_l false_l =
  match e with
  | Int n ->
      emit builder (Goto (if n = 0L then false_l else true_l))
  | Unary (UNot, inner) -> lower_cond env builder inner false_l true_l
  | Binary (LAnd, a, b) ->
      let mid_l = fresh_label builder "and_rhs" in
      lower_cond env builder a mid_l false_l;
      emit builder (Label mid_l);
      lower_cond env builder b true_l false_l
  | Binary (LOr, a, b) ->
      let mid_l = fresh_label builder "or_rhs" in
      lower_cond env builder a true_l mid_l;
      emit builder (Label mid_l);
      lower_cond env builder b true_l false_l
  | _ ->
      let cond = lower_expr env builder e in
      emit builder (IfZero (cond, false_l));
      emit builder (Goto true_l)

let lower_call_stmt env builder name args =
  let sig_ = lookup_func env name in
  let lowered_args = List.map (lower_expr env builder) args in
  match sig_.ret with
  | TVoid -> emit_op builder (Call (None, sig_.label, lowered_args))
  | TInt -> emit_op builder (Call (None, sig_.label, lowered_args))

let rec lower_stmt env builder = function
  | Block stmts ->
      push_scope env;
      List.iter (lower_stmt env builder) stmts;
      pop_scope env
  | Empty -> ()
  | Expr (Call (name, args)) -> lower_call_stmt env builder name args
  | Expr e -> ignore (lower_expr env builder e)
  | Assign (name, rhs) ->
      let value = lower_expr env builder rhs in
      emit_op builder (Store (lookup_name env name, value))
  | Decl d ->
      let init = lower_expr env builder d.init in
      emit_op builder (Store (Local d.ident.id, init));
      add_local env builder d.ident
  | If (cond, then_s, else_s) ->
      let then_l = fresh_label builder "if_then" in
      let else_l = fresh_label builder "if_else" in
      let end_l = fresh_label builder "if_end" in
      lower_cond env builder cond then_l else_l;
      emit builder (Label then_l);
      lower_stmt env builder then_s;
      emit builder (Goto end_l);
      emit builder (Label else_l);
      Option.iter (lower_stmt env builder) else_s;
      emit builder (Label end_l)
  | While (cond, body) ->
      let cond_l = fresh_label builder "while_cond" in
      let body_l = fresh_label builder "while_body" in
      let end_l = fresh_label builder "while_end" in
      emit builder (Label cond_l);
      lower_cond env builder cond body_l end_l;
      emit builder (Label body_l);
      env.break_labels <- end_l :: env.break_labels;
      env.continue_labels <- cond_l :: env.continue_labels;
      lower_stmt env builder body;
      env.break_labels <- List.tl env.break_labels;
      env.continue_labels <- List.tl env.continue_labels;
      emit builder (Goto cond_l);
      emit builder (Label end_l)
  | Break -> (
      match env.break_labels with
      | label :: _ -> emit builder (Goto label)
      | [] -> err "internal lowering break outside loop")
  | Continue -> (
      match env.continue_labels with
      | label :: _ -> emit builder (Goto label)
      | [] -> err "internal lowering continue outside loop")
  | Return None -> emit builder (Return None)
  | Return (Some e) -> emit builder (Return (Some (lower_expr env builder e)))

let lower_func globals funcs (f : Ast.func) =
  let label = Semant.func_label f.name.name in
  let entry = Printf.sprintf ".L_%s_entry" label in
  let builder =
    {
      func_label = label;
      next_temp = 0;
      next_label = 0;
      instrs_rev = [];
      locals_rev = [];
    }
  in
  let param_scope =
    List.fold_left
      (fun scope (param : Ast.ident) -> StringMap.add param.name (Local param.id) scope)
      StringMap.empty f.params
  in
  let env =
    {
      funcs;
      scopes = [ param_scope; globals ];
      break_labels = [];
      continue_labels = [];
    }
  in
  emit builder (Label entry);
  List.iter (lower_stmt env builder) f.body;
  emit builder
    (Return
       (match f.ret with
       | TInt -> Some (Imm 0L)
       | TVoid -> None));
  {
    ret = f.ret;
    name = f.name.name;
    label;
    entry;
    params = List.map (fun (p : Ast.ident) -> { id = p.id; name = p.name }) f.params;
    locals = List.rev builder.locals_rev;
    temp_count = builder.next_temp;
    body = List.rev builder.instrs_rev;
  }

let of_analysis (analysis : Semant.analysis) =
  let globals =
    List.fold_left
      (fun scope (g : Semant.global_decl) -> StringMap.add g.name (Global g.label) scope)
      StringMap.empty analysis.globals
  in
  let funcs =
    List.fold_left
      (fun acc top ->
        match top with
        | TopDecl _ -> acc
        | FuncDef f -> lower_func globals analysis.funcs f :: acc)
      [] analysis.program
  in
  { funcs = List.rev funcs }
