open Ast

exception Error of string

module StringMap = Map.Make (String)

type binding =
  | Local of int
  | Global of string

type layout = {
  offsets : (int, int) Hashtbl.t;
  call_slots : int array;
  frame_size : int;
}

type ctx = {
  buf : Buffer.t;
  offsets : (int, int) Hashtbl.t;
  call_slots : int array;
  globals : string StringMap.t;
  funcs : Semant.func_sig StringMap.t;
  epilogue : string;
  mutable label_id : int;
  mutable eval_depth : int;
  mutable scopes : binding StringMap.t list;
  mutable break_labels : string list;
  mutable continue_labels : string list;
}

let align16 n = ((n + 15) / 16) * 16

let emit ctx s =
  Buffer.add_string ctx.buf s;
  Buffer.add_char ctx.buf '\n'

let emitf ctx fmt = Printf.ksprintf (emit ctx) fmt

let fresh_label ctx prefix =
  let id = ctx.label_id in
  ctx.label_id <- ctx.label_id + 1;
  Printf.sprintf ".L%s_%d" prefix id

let push_reg ctx reg =
  emitf ctx "    addi sp, sp, -4";
  emitf ctx "    sw %s, 0(sp)" reg;
  ctx.eval_depth <- ctx.eval_depth + 4

let pop_reg ctx reg =
  if ctx.eval_depth < 4 then raise (Error "internal expression stack underflow");
  emitf ctx "    lw %s, 0(sp)" reg;
  emitf ctx "    addi sp, sp, 4";
  ctx.eval_depth <- ctx.eval_depth - 4

let lookup_offset (layout : layout) id =
  match Hashtbl.find_opt layout.offsets id with
  | Some off -> off
  | None -> raise (Error "internal missing stack slot")

let lookup_var ctx name =
  let rec find = function
    | [] -> None
    | scope :: rest -> (
        match StringMap.find_opt name scope with
        | Some b -> Some b
        | None -> find rest)
  in
  match find ctx.scopes with
  | Some b -> b
  | None -> (
      match StringMap.find_opt name ctx.globals with
      | Some label -> Global label
      | None -> raise (Error ("undefined identifier during codegen: " ^ name)))

let add_local ctx name off =
  match ctx.scopes with
  | scope :: rest -> ctx.scopes <- StringMap.add name (Local off) scope :: rest
  | [] -> raise (Error "internal empty scope stack")

let push_scope ctx = ctx.scopes <- StringMap.empty :: ctx.scopes

let pop_scope ctx =
  match ctx.scopes with
  | _ :: rest -> ctx.scopes <- rest
  | [] -> raise (Error "internal empty scope stack")

let rec max_args_expr = function
  | Int _ | Var _ -> 0
  | Unary (_, e) -> max_args_expr e
  | Binary (_, a, b) -> max (max_args_expr a) (max_args_expr b)
  | Call (_, args) ->
      List.fold_left (fun m e -> max m (max_args_expr e)) (List.length args) args

let max_args_decl d = max_args_expr d.init

let rec max_args_stmt = function
  | Block stmts -> max_args_stmts stmts
  | Empty | Break | Continue -> 0
  | Expr e | Assign (_, e) -> max_args_expr e
  | Decl d -> max_args_decl d
  | If (cond, t, e) ->
      max (max_args_expr cond)
        (max (max_args_stmt t) (Option.value (Option.map max_args_stmt e) ~default:0))
  | While (cond, body) -> max (max_args_expr cond) (max_args_stmt body)
  | Return None -> 0
  | Return (Some e) -> max_args_expr e

and max_args_stmts stmts =
  List.fold_left (fun m s -> max m (max_args_stmt s)) 0 stmts

let compute_layout f =
  let offsets = Hashtbl.create 64 in
  let next = ref 12 in
  let alloc_slot () =
    let off = - !next in
    next := !next + 4;
    off
  in
  let alloc_ident id = Hashtbl.add offsets id (alloc_slot ()) in
  List.iter (fun p -> alloc_ident p.id) f.params;
  let rec walk_stmt = function
    | Block stmts -> List.iter walk_stmt stmts
    | Decl d ->
        alloc_ident d.ident.id;
        walk_expr d.init
    | Expr e | Assign (_, e) | Return (Some e) -> walk_expr e
    | If (cond, t, e) ->
        walk_expr cond;
        walk_stmt t;
        Option.iter walk_stmt e
    | While (cond, body) ->
        walk_expr cond;
        walk_stmt body
    | Empty | Break | Continue | Return None -> ()
  and walk_expr = function
    | Int _ | Var _ -> ()
    | Unary (_, e) -> walk_expr e
    | Binary (_, a, b) ->
        walk_expr a;
        walk_expr b
    | Call (_, args) -> List.iter walk_expr args
  in
  List.iter walk_stmt f.body;
  let max_args = max_args_stmts f.body in
  let call_slots = Array.init max_args (fun _ -> alloc_slot ()) in
  let frame_bytes = !next - 4 in
  { offsets; call_slots; frame_size = align16 frame_bytes }

let load_binding ctx dst = function
  | Local off -> emitf ctx "    lw %s, %d(s0)" dst off
  | Global label ->
      emitf ctx "    la t1, %s" label;
      emitf ctx "    lw %s, 0(t1)" dst

let store_binding ctx src = function
  | Local off -> emitf ctx "    sw %s, %d(s0)" src off
  | Global label ->
      emitf ctx "    la t1, %s" label;
      emitf ctx "    sw %s, 0(t1)" src

let func_label ctx name =
  match StringMap.find_opt name ctx.funcs with
  | Some f -> f.label
  | None -> raise (Error ("unknown function during codegen: " ^ name))

let rec gen_simple ctx dst = function
  | Int n ->
      emitf ctx "    li %s, %Ld" dst n;
      true
  | Var name ->
      load_binding ctx dst (lookup_var ctx name);
      true
  | Unary (op, e) ->
      if gen_simple ctx dst e then (
        (match op with
        | UPlus -> ()
        | UMinus -> emitf ctx "    neg %s, %s" dst dst
        | UNot -> emitf ctx "    sltiu %s, %s, 1" dst dst);
        true)
      else false
  | _ -> false

let emit_binop ctx op dst src =
  match op with
  | Add -> emitf ctx "    add %s, %s, %s" dst dst src
  | Sub -> emitf ctx "    sub %s, %s, %s" dst dst src
  | Mul -> emitf ctx "    mul %s, %s, %s" dst dst src
  | Div -> emitf ctx "    div %s, %s, %s" dst dst src
  | Mod -> emitf ctx "    rem %s, %s, %s" dst dst src
  | Lt -> emitf ctx "    slt %s, %s, %s" dst dst src
  | Gt -> emitf ctx "    slt %s, %s, %s" dst src dst
  | Le ->
      emitf ctx "    slt %s, %s, %s" dst src dst;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Ge ->
      emitf ctx "    slt %s, %s, %s" dst dst src;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Eq ->
      emitf ctx "    sub %s, %s, %s" dst dst src;
      emitf ctx "    sltiu %s, %s, 1" dst dst
  | Ne ->
      emitf ctx "    sub %s, %s, %s" dst dst src;
      emitf ctx "    sltu %s, x0, %s" dst dst
  | LAnd | LOr -> raise (Error "internal logical operator lowering error")

let rec gen_expr ctx = function
  | Int n ->
      emitf ctx "    li t0, %Ld" n;
      push_reg ctx "t0"
  | Var name ->
      load_binding ctx "t0" (lookup_var ctx name);
      push_reg ctx "t0"
  | Unary (op, e) ->
      gen_expr ctx e;
      pop_reg ctx "t0";
      (match op with
      | UPlus -> ()
      | UMinus -> emit ctx "    neg t0, t0"
      | UNot -> emit ctx "    sltiu t0, t0, 1");
      push_reg ctx "t0"
  | Binary (LAnd, a, b) -> gen_logical_and ctx a b
  | Binary (LOr, a, b) -> gen_logical_or ctx a b
  | Binary (op, a, b) ->
      gen_expr ctx a;
      gen_expr ctx b;
      pop_reg ctx "t1";
      pop_reg ctx "t0";
      gen_binop ctx op;
      push_reg ctx "t0"
  | Call (name, args) -> gen_call ctx name args

and gen_binop ctx op = emit_binop ctx op "t0" "t1"

and gen_logical_and ctx a b =
  let false_l = fresh_label ctx "and_false" in
  let end_l = fresh_label ctx "and_end" in
  gen_expr ctx a;
  pop_reg ctx "t0";
  emitf ctx "    beqz t0, %s" false_l;
  gen_expr ctx b;
  pop_reg ctx "t0";
  emitf ctx "    beqz t0, %s" false_l;
  emit ctx "    li t0, 1";
  emitf ctx "    j %s" end_l;
  emitf ctx "%s:" false_l;
  emit ctx "    li t0, 0";
  emitf ctx "%s:" end_l;
  push_reg ctx "t0"

and gen_logical_or ctx a b =
  let true_l = fresh_label ctx "or_true" in
  let end_l = fresh_label ctx "or_end" in
  gen_expr ctx a;
  pop_reg ctx "t0";
  emitf ctx "    bnez t0, %s" true_l;
  gen_expr ctx b;
  pop_reg ctx "t0";
  emitf ctx "    bnez t0, %s" true_l;
  emit ctx "    li t0, 0";
  emitf ctx "    j %s" end_l;
  emitf ctx "%s:" true_l;
  emit ctx "    li t0, 1";
  emitf ctx "%s:" end_l;
  push_reg ctx "t0"

and gen_call ctx name args =
  let argc = List.length args in
  if argc > Array.length ctx.call_slots then
    raise (Error "internal missing call argument spill slots");
  List.iteri
    (fun i arg ->
      gen_expr ctx arg;
      pop_reg ctx "t0";
      emitf ctx "    sw t0, %d(s0)" ctx.call_slots.(i))
    args;
  let regc = min argc 8 in
  for i = 0 to regc - 1 do
    emitf ctx "    lw a%d, %d(s0)" i ctx.call_slots.(i)
  done;
  let extra = max 0 (argc - 8) in
  let raw_area = extra * 4 in
  let pad = (16 - ((ctx.eval_depth + raw_area) mod 16)) mod 16 in
  let call_area = raw_area + pad in
  if call_area > 0 then emitf ctx "    addi sp, sp, -%d" call_area;
  for i = 8 to argc - 1 do
    emitf ctx "    lw t0, %d(s0)" ctx.call_slots.(i);
    emitf ctx "    sw t0, %d(sp)" ((i - 8) * 4)
  done;
  emitf ctx "    call %s" (func_label ctx name);
  if call_area > 0 then emitf ctx "    addi sp, sp, %d" call_area;
  push_reg ctx "a0"

let rec reg_need = function
  | Int _ | Var _ -> Some 1
  | Unary (_, e) -> reg_need e
  | Call _ | Binary (LAnd, _, _) | Binary (LOr, _, _) -> None
  | Binary (_, a, b) -> (
      match (reg_need a, reg_need b) with
      | Some left, Some right -> Some (max left (right + 1))
      | _ -> None)

let rec gen_reg ctx regs = function
  | Int n ->
      emitf ctx "    li %s, %Ld" (List.hd regs) n
  | Var name ->
      let dst = List.hd regs in
      load_binding ctx dst (lookup_var ctx name)
  | Unary (op, e) ->
      gen_reg ctx regs e;
      let dst = List.hd regs in
      (match op with
      | UPlus -> ()
      | UMinus -> emitf ctx "    neg %s, %s" dst dst
      | UNot -> emitf ctx "    sltiu %s, %s, 1" dst dst)
  | Binary (op, a, b) -> (
      match regs with
      | dst :: src :: rest ->
          gen_reg ctx regs a;
          gen_reg ctx (src :: rest) b;
          emit_binop ctx op dst src
      | _ -> raise (Error "not enough registers for expression"))
  | Call _ -> raise (Error "function call in register expression")

let gen_value ctx dst e =
  if not (gen_simple ctx dst e) then
    match reg_need e with
    | Some need when need <= 3 ->
        gen_reg ctx [ "t0"; "t1"; "t2" ] e;
        if dst <> "t0" then emitf ctx "    addi %s, t0, 0" dst
    | _ ->
        gen_expr ctx e;
        pop_reg ctx dst

let rec gen_stmt ctx = function
  | Block stmts -> gen_block ctx stmts
  | Empty -> ()
  | Expr e -> gen_value ctx "t0" e
  | Assign (name, rhs) ->
      gen_value ctx "t0" rhs;
      store_binding ctx "t0" (lookup_var ctx name)
  | Decl d ->
      gen_value ctx "t0" d.init;
      let off = Hashtbl.find ctx.offsets d.ident.id in
      emitf ctx "    sw t0, %d(s0)" off;
      add_local ctx d.ident.name off
  | If (cond, then_s, else_s) ->
      let else_l = fresh_label ctx "else" in
      let end_l = fresh_label ctx "ifend" in
      gen_value ctx "t0" cond;
      emitf ctx "    beqz t0, %s" else_l;
      gen_stmt ctx then_s;
      emitf ctx "    j %s" end_l;
      emitf ctx "%s:" else_l;
      Option.iter (gen_stmt ctx) else_s;
      emitf ctx "%s:" end_l
  | While (cond, body) ->
      let start_l = fresh_label ctx "while" in
      let end_l = fresh_label ctx "wend" in
      emitf ctx "%s:" start_l;
      gen_value ctx "t0" cond;
      emitf ctx "    beqz t0, %s" end_l;
      ctx.break_labels <- end_l :: ctx.break_labels;
      ctx.continue_labels <- start_l :: ctx.continue_labels;
      gen_stmt ctx body;
      ctx.break_labels <- List.tl ctx.break_labels;
      ctx.continue_labels <- List.tl ctx.continue_labels;
      emitf ctx "    j %s" start_l;
      emitf ctx "%s:" end_l
  | Break -> (
      match ctx.break_labels with
      | label :: _ -> emitf ctx "    j %s" label
      | [] -> raise (Error "break outside loop"))
  | Continue -> (
      match ctx.continue_labels with
      | label :: _ -> emitf ctx "    j %s" label
      | [] -> raise (Error "continue outside loop"))
  | Return None -> emitf ctx "    j %s" ctx.epilogue
  | Return (Some e) ->
      gen_value ctx "a0" e;
      emitf ctx "    j %s" ctx.epilogue

and gen_block ctx stmts =
  push_scope ctx;
  List.iter (gen_stmt ctx) stmts;
  pop_scope ctx

let gen_func buf globals funcs (f : Ast.func) =
  let layout = compute_layout f in
  let epilogue = Printf.sprintf ".L_%s_epilogue" (Semant.func_label f.name.name) in
  let param_scope =
    List.fold_left
      (fun scope (p : Ast.ident) ->
        StringMap.add p.name (Local (lookup_offset layout p.id)) scope)
      StringMap.empty f.params
  in
  let ctx =
    {
      buf;
      offsets = layout.offsets;
      call_slots = layout.call_slots;
      globals;
      funcs;
      epilogue;
      label_id = 0;
      eval_depth = 0;
      scopes = [ param_scope ];
      break_labels = [];
      continue_labels = [];
    }
  in
  let label = Semant.func_label f.name.name in
  emit ctx "    .text";
  emit ctx "    .align 2";
  if f.name.name = "main" then emit ctx "    .globl main";
  emitf ctx "%s:" label;
  emitf ctx "    addi sp, sp, -%d" layout.frame_size;
  emitf ctx "    sw ra, %d(sp)" (layout.frame_size - 4);
  emitf ctx "    sw s0, %d(sp)" (layout.frame_size - 8);
  emitf ctx "    addi s0, sp, %d" layout.frame_size;
  List.iteri
    (fun i (p : Ast.ident) ->
      let off = lookup_offset layout p.id in
      if i < 8 then emitf ctx "    sw a%d, %d(s0)" i off
      else (
        emitf ctx "    lw t0, %d(s0)" ((i - 8) * 4);
        emitf ctx "    sw t0, %d(s0)" off))
    f.params;
  gen_block ctx f.body;
  (match f.ret with
  | TInt -> emit ctx "    li a0, 0"
  | TVoid -> ());
  emitf ctx "%s:" epilogue;
  if ctx.eval_depth <> 0 then raise (Error "internal expression stack leak");
  emitf ctx "    lw ra, %d(sp)" (layout.frame_size - 4);
  emitf ctx "    lw s0, %d(sp)" (layout.frame_size - 8);
  emitf ctx "    addi sp, sp, %d" layout.frame_size;
  emit ctx "    ret";
  emit ctx ""

let emit_global buf g =
  Buffer.add_string buf "    .data\n";
  Buffer.add_string buf "    .align 2\n";
  Buffer.add_string buf (g.Semant.label ^ ":\n");
  Buffer.add_string buf (Printf.sprintf "    .word %Ld\n\n" g.Semant.init)

let generate (analysis : Semant.analysis) =
  let buf = Buffer.create 16384 in
  Buffer.add_string buf "    .option nopic\n\n";
  List.iter (emit_global buf) analysis.globals;
  let globals =
    List.fold_left
      (fun m (g : Semant.global_decl) -> StringMap.add g.name g.label m)
      StringMap.empty analysis.globals
  in
  List.iter
    (function
      | TopDecl _ -> ()
      | FuncDef f -> gen_func buf globals analysis.funcs f)
    analysis.program;
  Buffer.contents buf
