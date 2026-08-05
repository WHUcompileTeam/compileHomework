open Ast

exception Error of string

module StringMap = Map.Make (String)

type layout = {
  local_offsets : (int, int) Hashtbl.t;
  temp_offsets : (int, int) Hashtbl.t;
  frame_size : int;
  outgoing_area : int;
}

type ctx = {
  buf : Buffer.t;
  local_offsets : (int, int) Hashtbl.t;
  temp_offsets : (int, int) Hashtbl.t;
  epilogue : string;
}

let global_addr_reg = "t3"

let align16 n = ((n + 15) / 16) * 16

let emit ctx s =
  Buffer.add_string ctx.buf s;
  Buffer.add_char ctx.buf '\n'

let emitf ctx fmt = Printf.ksprintf (emit ctx) fmt

let lookup_offset table id kind =
  match Hashtbl.find_opt table id with
  | Some off -> off
  | None -> raise (Error ("internal missing " ^ kind ^ " slot"))

let max_call_args (f : Cfg.func) =
  List.fold_left
    (fun current (block : Cfg.block) ->
      List.fold_left
        (fun acc instr ->
          match instr with
          | Tcg.Call (_, _, args) -> max acc (List.length args)
          | _ -> acc)
        current block.body)
    0 f.blocks

let compute_layout (f : Cfg.func) =
  let local_offsets = Hashtbl.create 64 in
  let temp_offsets = Hashtbl.create (max 8 f.temp_count) in
  let next = ref 12 in
  let alloc_slot () =
    let off = - !next in
    next := !next + 4;
    off
  in
  let alloc_local (var : Tcg.var) =
    if not (Hashtbl.mem local_offsets var.id) then
      Hashtbl.add local_offsets var.id (alloc_slot ())
  in
  List.iter alloc_local f.params;
  List.iter alloc_local f.locals;
  for temp = 0 to f.temp_count - 1 do
    Hashtbl.add temp_offsets temp (alloc_slot ())
  done;
  let extra_args = max 0 (max_call_args f - 8) in
  let outgoing_area = align16 (extra_args * 4) in
  let frame_bytes = outgoing_area + (!next - 4) in
  {
    local_offsets;
    temp_offsets;
    frame_size = align16 frame_bytes;
    outgoing_area;
  }

let load_operand ctx dst = function
  | Tcg.Imm n -> emitf ctx "    li %s, %Ld" dst n
  | Tcg.Temp temp ->
      emitf ctx "    lw %s, %d(s0)" dst (lookup_offset ctx.temp_offsets temp "temp")

let store_temp ctx temp src =
  emitf ctx "    sw %s, %d(s0)" src (lookup_offset ctx.temp_offsets temp "temp")

let load_place ctx dst = function
  | Tcg.Local id ->
      emitf ctx "    lw %s, %d(s0)" dst (lookup_offset ctx.local_offsets id "local")
  | Tcg.Global label ->
      emitf ctx "    la %s, %s" global_addr_reg label;
      emitf ctx "    lw %s, 0(%s)" dst global_addr_reg

let store_place ctx src = function
  | Tcg.Local id ->
      emitf ctx "    sw %s, %d(s0)" src (lookup_offset ctx.local_offsets id "local")
  | Tcg.Global label ->
      emitf ctx "    la %s, %s" global_addr_reg label;
      emitf ctx "    sw %s, 0(%s)" src global_addr_reg

let emit_unop ctx op =
  match op with
  | UPlus -> ()
  | UMinus -> emit ctx "    neg t0, t0"
  | UNot -> emit ctx "    sltiu t0, t0, 1"

let emit_binop ctx op dst lhs rhs =
  match op with
  | Add -> emitf ctx "    add %s, %s, %s" dst lhs rhs
  | Sub -> emitf ctx "    sub %s, %s, %s" dst lhs rhs
  | Mul -> emitf ctx "    mul %s, %s, %s" dst lhs rhs
  | Div -> emitf ctx "    div %s, %s, %s" dst lhs rhs
  | Mod -> emitf ctx "    rem %s, %s, %s" dst lhs rhs
  | Lt -> emitf ctx "    slt %s, %s, %s" dst lhs rhs
  | Gt -> emitf ctx "    slt %s, %s, %s" dst rhs lhs
  | Le ->
      emitf ctx "    slt %s, %s, %s" dst rhs lhs;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Ge ->
      emitf ctx "    slt %s, %s, %s" dst lhs rhs;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Eq ->
      emitf ctx "    sub %s, %s, %s" dst lhs rhs;
      emitf ctx "    sltiu %s, %s, 1" dst dst
  | Ne ->
      emitf ctx "    sub %s, %s, %s" dst lhs rhs;
      emitf ctx "    sltu %s, x0, %s" dst dst
  | LAnd | LOr -> raise (Error "logical operators should not reach binary lowering")

let gen_simple_instr ctx = function
  | Tcg.Move (dst, src) ->
      load_operand ctx "t0" src;
      store_temp ctx dst "t0"
  | Tcg.Un (dst, op, src) ->
      load_operand ctx "t0" src;
      emit_unop ctx op;
      store_temp ctx dst "t0"
  | Tcg.Bin (dst, op, lhs, rhs) ->
      load_operand ctx "t0" lhs;
      load_operand ctx "t1" rhs;
      emit_binop ctx op "t2" "t0" "t1";
      store_temp ctx dst "t2"
  | Tcg.Load (dst, place) ->
      load_place ctx "t0" place;
      store_temp ctx dst "t0"
  | Tcg.Store (place, value) ->
      load_operand ctx "t0" value;
      store_place ctx "t0" place
  | Tcg.Call (dst, callee, args) ->
      List.iteri
        (fun i arg ->
          if i < 8 then load_operand ctx (Printf.sprintf "a%d" i) arg
          else (
            load_operand ctx "t0" arg;
            emitf ctx "    sw t0, %d(sp)" ((i - 8) * 4)))
        args;
      emitf ctx "    call %s" callee;
      Option.iter (fun temp -> store_temp ctx temp "a0") dst

let emit_jump_if_needed ctx next_label target =
  if next_label <> Some target then emitf ctx "    j %s" target

let emit_branch_result ctx reg if_true if_false next_label =
  if next_label = Some if_false then emitf ctx "    bnez %s, %s" reg if_true
  else if next_label = Some if_true then emitf ctx "    beqz %s, %s" reg if_false
  else (
    emitf ctx "    bnez %s, %s" reg if_true;
    emitf ctx "    j %s" if_false)

let gen_terminator ctx next_label = function
  | Cfg.Jump label -> emit_jump_if_needed ctx next_label label
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      load_operand ctx "t0" cond;
      emit_branch_result ctx "t0" if_nonzero if_zero next_label
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      load_operand ctx "t0" cond;
      emit_branch_result ctx "t0" if_nonzero if_zero next_label
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      load_operand ctx "t0" lhs;
      load_operand ctx "t1" rhs;
      emit_binop ctx op "t2" "t0" "t1";
      emit_branch_result ctx "t2" if_true if_false next_label
  | Cfg.Return None -> emitf ctx "    j %s" ctx.epilogue
  | Cfg.Return (Some value) ->
      load_operand ctx "a0" value;
      emitf ctx "    j %s" ctx.epilogue

let gen_block ctx next_label (block : Cfg.block) =
  emitf ctx "%s:" block.label;
  List.iter (gen_simple_instr ctx) block.body;
  gen_terminator ctx next_label block.term

let gen_func buf (f : Cfg.func) =
  let layout = compute_layout f in
  let epilogue = Printf.sprintf ".L_%s_epilogue" f.label in
  let ctx =
    {
      buf;
      local_offsets = layout.local_offsets;
      temp_offsets = layout.temp_offsets;
      epilogue;
    }
  in
  emit ctx "    .text";
  emit ctx "    .align 2";
  if f.name = "main" then emit ctx "    .globl main";
  emitf ctx "%s:" f.label;
  emitf ctx "    addi sp, sp, -%d" layout.frame_size;
  emitf ctx "    sw ra, %d(sp)" (layout.frame_size - 4);
  emitf ctx "    sw s0, %d(sp)" (layout.frame_size - 8);
  emitf ctx "    addi s0, sp, %d" layout.frame_size;
  List.iteri
    (fun i (param : Tcg.var) ->
      let off = lookup_offset layout.local_offsets param.id "local" in
      if i < 8 then emitf ctx "    sw a%d, %d(s0)" i off
      else (
        emitf ctx "    lw t0, %d(s0)" ((i - 8) * 4);
        emitf ctx "    sw t0, %d(s0)" off))
    f.params;
  let rec emit_blocks = function
    | [] -> ()
    | [ block ] -> gen_block ctx None block
    | block :: ((next_block :: _) as rest) ->
        gen_block ctx (Some next_block.label) block;
        emit_blocks rest
  in
  emit_blocks f.blocks;
  emitf ctx "%s:" epilogue;
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

let generate (analysis : Semant.analysis) (cfg : Cfg.program) =
  let buf = Buffer.create 16384 in
  Buffer.add_string buf "    .option nopic\n\n";
  List.iter (emit_global buf) analysis.globals;
  List.iter (gen_func buf) cfg.funcs;
  Buffer.contents buf
