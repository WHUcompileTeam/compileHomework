let trim = String.trim

let starts_with s prefix =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix

let split_ws s =
  s |> trim |> String.split_on_char ' ' |> List.filter (fun p -> p <> "")

let strip_trailing_comma s =
  let len = String.length s in
  if len > 0 && s.[len - 1] = ',' then String.sub s 0 (len - 1) else s

let parse_push l1 l2 =
  match (split_ws l1, split_ws l2) with
  | [ "addi"; "sp,"; "sp,"; "-4" ], [ "sw"; reg_comma; "0(sp)" ] ->
      Some (strip_trailing_comma reg_comma)
  | _ -> None

let parse_pop l1 l2 =
  match (split_ws l1, split_ws l2) with
  | [ "lw"; reg_comma; "0(sp)" ], [ "addi"; "sp,"; "sp,"; "4" ] ->
      Some (strip_trailing_comma reg_comma)
  | _ -> None

let parse_move line =
  match split_ws line with
  | [ "addi"; dst_comma; src_comma; "0" ] ->
      Some (strip_trailing_comma dst_comma, strip_trailing_comma src_comma)
  | _ -> None

let is_label line =
  let s = trim line in
  s <> "" && s.[String.length s - 1] = ':'

let label_name line =
  let s = trim line in
  String.sub s 0 (String.length s - 1)

let is_jump_to line label =
  trim line = "j " ^ label

let move_line dst src =
  if dst = src then None else Some (Printf.sprintf "    addi %s, %s, 0" dst src)

let rec emit_opt_lines acc = function
  | [] -> acc
  | None :: rest -> emit_opt_lines acc rest
  | Some line :: rest -> emit_opt_lines (line :: acc) rest

let split_lines asm =
  match List.rev (String.split_on_char '\n' asm) with
  | "" :: rest -> List.rev rest
  | rev_lines -> List.rev rev_lines

(* -------------------------------------------------------------------------- *)
(* Physical-register liveness used by the addi-chain peephole.                *)
(*                                                                            *)
(* We deliberately keep this analysis conservative: unknown instructions read  *)
(* every register they mention, calls read argument registers and clobber the   *)
(* normal caller-saved set, and branches get real CFG successors.              *)
(* -------------------------------------------------------------------------- *)

module RegSet = Set.Make (String)

let all_registers =
  [
    "x0"; "ra"; "sp"; "gp"; "tp";
    "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6";
    "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11";
    "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
  ]

let is_register reg = List.mem reg all_registers

let value_register reg =
  reg <> "x0" && reg <> "sp" && reg <> "gp" && reg <> "tp" && is_register reg

let regset_of_list regs =
  List.fold_left (fun set reg -> RegSet.add reg set) RegSet.empty regs

let caller_saved_regs =
  regset_of_list
    [
      "ra";
      "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6";
      "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
    ]

let call_arg_regs =
  regset_of_list [ "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" ]

let normalize_asm_punct s =
  String.map
    (fun c ->
      match c with
      | ',' | '(' | ')' -> ' '
      | _ -> c)
    s

let split_asm_words line =
  line |> normalize_asm_punct |> split_ws

let registers_in words =
  List.fold_left
    (fun set word -> if is_register word then RegSet.add word set else set)
    RegSet.empty words

let first_and_rest = function
  | [] -> (None, [])
  | head :: rest -> (Some head, rest)

let is_int64_literal s =
  try
    ignore (Int64.of_string s);
    true
  with _ -> false

let uses_defs line =
  let s = trim line in
  if s = "" || is_label line || starts_with s "." then (RegSet.empty, RegSet.empty)
  else
    match split_asm_words line with
    | [] -> (RegSet.empty, RegSet.empty)
    | opcode :: operands ->
        let operand_regs = registers_in operands in
        let def_first () =
          match first_and_rest operands with
          | Some dst, rest when is_register dst ->
              (registers_in rest, RegSet.singleton dst)
          | _ -> (operand_regs, RegSet.empty)
        in
        begin
          match opcode with
          | "li" | "la" -> (
              match operands with
              | dst :: _ when is_register dst -> (RegSet.empty, RegSet.singleton dst)
              | _ -> (operand_regs, RegSet.empty))
          | "lw" | "addi" | "add" | "sub" | "mul" | "div" | "rem"
          | "slt" | "sltu" | "slti" | "sltiu"
          | "slli" | "srli" | "srai"
          | "andi" | "xor" | "xori" | "neg" ->
              def_first ()
          | "sw" -> (
              match operands with
              | [ src; symbol; scratch ]
                when is_register src
                     && is_register scratch
                     && not (is_int64_literal symbol) ->
                  (* GNU pseudo: sw rs, symbol, scratch.
                     rs is read; scratch is clobbered by the AUIPC expansion. *)
                  (RegSet.singleton src, RegSet.singleton scratch)
              | _ ->
                  (operand_regs, RegSet.empty))
          | "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"
          | "beqz" | "bnez" ->
              (operand_regs, RegSet.empty)
          | "j" ->
              (RegSet.empty, RegSet.empty)
          | "call" ->
              (call_arg_regs, caller_saved_regs)
          | "ret" ->
              (* Be conservative about the integer return-value register.
                 This is required by post-regalloc dead-move elimination:
                 [addi a0, r, 0; ret] must keep the write to [a0].  Void
                 functions may not need [a0], but treating it as live is safe. *)
              (regset_of_list [ "ra"; "a0" ], RegSet.empty)
          | _ ->
              (* Unknown instruction: assume every mentioned register is read.
                 This may miss optimization opportunities, but cannot make the
                 addi-chain transformation less safe. *)
              (operand_regs, RegSet.empty)
        end

let branch_target line =
  match split_asm_words line with
  | [ "j"; target ] -> Some target
  | [ ("beqz" | "bnez"); _; target ] -> Some target
  | [ ("beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"); _; _; target ] ->
      Some target
  | _ -> None

let is_unconditional_jump line =
  match split_asm_words line with
  | [ "j"; _ ] -> true
  | _ -> false

let is_conditional_branch line =
  match split_asm_words line with
  | [ ("beqz" | "bnez"); _; _ ] -> true
  | [ ("beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"); _; _; _ ] -> true
  | _ -> false

let is_return line =
  match split_asm_words line with
  | [ "ret" ] -> true
  | _ -> false

let compute_live_out lines =
  let n = Array.length lines in
  let label_pos = Hashtbl.create 32 in
  Array.iteri
    (fun i line ->
      if is_label line then Hashtbl.replace label_pos (label_name line) i)
    lines;
  let uses = Array.make n RegSet.empty in
  let defs = Array.make n RegSet.empty in
  Array.iteri
    (fun i line ->
      let use_set, def_set = uses_defs line in
      uses.(i) <- use_set;
      defs.(i) <- def_set)
    lines;
  let live_in = Array.make n RegSet.empty in
  let live_out = Array.make n RegSet.empty in
  let fallthrough i = if i + 1 < n then [ i + 1 ] else [] in
  let successors i =
    let line = lines.(i) in
    if is_return line then []
    else if is_unconditional_jump line then
      begin
        match branch_target line with
        | Some target -> (
            match Hashtbl.find_opt label_pos target with
            | Some pos -> [ pos ]
            | None -> [])
        | None -> []
      end
    else if is_conditional_branch line then
      let branch_succ =
        match branch_target line with
        | Some target -> (
            match Hashtbl.find_opt label_pos target with
            | Some pos -> [ pos ]
            | None -> [])
        | None -> []
      in
      branch_succ @ fallthrough i
    else fallthrough i
  in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = n - 1 downto 0 do
      let out_set =
        List.fold_left
          (fun acc succ ->
            if succ >= 0 && succ < n then RegSet.union acc live_in.(succ) else acc)
          RegSet.empty (successors i)
      in
      let in_set =
        RegSet.union uses.(i) (RegSet.diff out_set defs.(i))
      in
      if not (RegSet.equal out_set live_out.(i)) then (
        live_out.(i) <- out_set;
        changed := true);
      if not (RegSet.equal in_set live_in.(i)) then (
        live_in.(i) <- in_set;
        changed := true)
    done
  done;
  live_out

let parse_int64 s =
  try Some (Int64.of_string s) with _ -> None

let parse_addi line =
  match split_asm_words line with
  | [ "addi"; dst; src; imm ] when is_register dst && is_register src -> (
      match parse_int64 imm with
      | Some value -> Some (dst, src, value)
      | None -> None)
  | _ -> None

let fits_simm12 value =
  Int64.compare value (-2048L) >= 0 && Int64.compare value 2047L <= 0

let addi_line dst src imm =
  Printf.sprintf "    addi %s, %s, %Ld" dst src imm

let debug_addi_chain =
  Sys.getenv_opt "TOYC_DEBUG_ASM_ADDI_CHAIN" <> None

let debug_dead_move =
  Sys.getenv_opt "TOYC_DEBUG_ASM_DEAD_MOVE" <> None

let can_fold_addi_chain live_out second_index mid base dst imm1 imm2 =
  let combined = Int64.add imm1 imm2 in
  value_register mid
  && value_register base
  && value_register dst
  && fits_simm12 combined
  && (dst = mid || not (RegSet.mem mid live_out.(second_index)))

let peephole_pass asm =
  let lines = asm |> split_lines |> Array.of_list in
  let n = Array.length lines in
  let live_out = compute_live_out lines in
  let rec loop i acc =
    if i >= n then List.rev acc
    else if
      i + 3 < n
      && Option.is_some (parse_push lines.(i) lines.(i + 1))
      && Option.is_some (parse_pop lines.(i + 2) lines.(i + 3))
    then
      let src = Option.get (parse_push lines.(i) lines.(i + 1)) in
      let dst = Option.get (parse_pop lines.(i + 2) lines.(i + 3)) in
      let acc' =
        match move_line dst src with
        | None -> acc
        | Some line -> line :: acc
      in
      loop (i + 4) acc'
    else if i + 1 < n then
      match (parse_addi lines.(i), parse_addi lines.(i + 1)) with
      | Some (mid, base, imm1), Some (dst, src2, imm2)
        when src2 = mid
             && can_fold_addi_chain live_out (i + 1) mid base dst imm1 imm2 ->
          let combined = Int64.add imm1 imm2 in
          if debug_addi_chain then
            Printf.eprintf
              "asm-addi-chain line=%d mid=%s base=%s dst=%s imm=%Ld+%Ld->%Ld\n%!"
              (i + 1) mid base dst imm1 imm2 combined;
          loop (i + 2) (addi_line dst base combined :: acc)
      | _ -> (
          match (parse_move lines.(i), parse_move lines.(i + 1)) with
          | Some (dst1, src1), Some (dst2, src2) when dst1 = dst2 ->
              if src2 = dst2 then
                let acc' = emit_opt_lines acc [ move_line dst1 src1 ] in
                loop (i + 2) acc'
              else loop (i + 1) acc
          | Some (dst1, src1), Some (dst2, src2) when src2 = dst1 ->
              let acc' =
                emit_opt_lines acc [ move_line dst1 src1; move_line dst2 src1 ]
              in
              loop (i + 2) acc'
          | _ -> loop_tail i acc)
    else loop_tail i acc
  and loop_tail i acc =
    match parse_move lines.(i) with
    | Some (dst, _src)
      when value_register dst && not (RegSet.mem dst live_out.(i)) ->
        if debug_dead_move then
          Printf.eprintf "asm-dead-move line=%d dst=%s instr=%s\n%!"
            (i + 1) dst (trim lines.(i));
        loop (i + 1) acc
    | _ ->
        if i + 1 < n && starts_with (trim lines.(i)) "j " && is_label lines.(i + 1) then
          let label = label_name lines.(i + 1) in
          if is_jump_to lines.(i) label then loop (i + 1) acc
          else loop (i + 1) (lines.(i) :: acc)
        else loop (i + 1) (lines.(i) :: acc)
  in
  String.concat "\n" (loop 0 []) ^ "\n"

(* -------------------------------------------------------------------------- *)
(* #10 final generic post-RA machine cleanup.                                 *)
(*                                                                            *)
(* These rules are workload-independent and only fire when they strictly      *)
(* remove machine instructions or redirect control flow without changing      *)
(* semantics.  They run after the older peephole pass and participate in the  *)
(* same fixed point.                                                          *)
(* -------------------------------------------------------------------------- *)

let item10_final_asm_cleanup_enabled () =
  Sys.getenv_opt "TOYC_DISABLE_ITEM10_FINAL_ASM_CLEANUP" = None

let item10_parse_li line =
  match split_asm_words line with
  | [ "li"; dst; imm ] when is_register dst -> (
      match parse_int64 imm with
      | Some value -> Some (dst, value)
      | None -> None)
  | _ -> None

let item10_positive_pow2_shift value =
  if Int64.compare value 0L <= 0 then None
  else
    let rec loop v shift =
      if v = 1L then Some shift
      else if Int64.logand v 1L <> 0L then None
      else if shift >= 31 then None
      else loop (Int64.shift_right_logical v 1) (shift + 1)
    in
    loop value 0

type item10_branch =
  | Item10BranchZero of string * string * string
  | Item10BranchBinary of string * string * string * string

let item10_parse_branch line =
  match split_asm_words line with
  | [ (("beqz" | "bnez") as opcode); reg; target ] ->
      Some (Item10BranchZero (opcode, reg, target))
  | [ (("beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu") as opcode);
      lhs; rhs; target ] ->
      Some (Item10BranchBinary (opcode, lhs, rhs, target))
  | _ -> None

let item10_branch_line = function
  | Item10BranchZero (opcode, reg, target) ->
      Printf.sprintf "    %s %s, %s" opcode reg target
  | Item10BranchBinary (opcode, lhs, rhs, target) ->
      Printf.sprintf "    %s %s, %s, %s" opcode lhs rhs target

let item10_replace_branch_reg branch old_reg new_reg =
  match branch with
  | Item10BranchZero (opcode, reg, target) ->
      Item10BranchZero
        (opcode, (if reg = old_reg then new_reg else reg), target)
  | Item10BranchBinary (opcode, lhs, rhs, target) ->
      Item10BranchBinary
        ( opcode,
          (if lhs = old_reg then new_reg else lhs),
          (if rhs = old_reg then new_reg else rhs),
          target )

let item10_replace_branch_target branch new_target =
  match branch with
  | Item10BranchZero (opcode, reg, _) ->
      Item10BranchZero (opcode, reg, new_target)
  | Item10BranchBinary (opcode, lhs, rhs, _) ->
      Item10BranchBinary (opcode, lhs, rhs, new_target)

let item10_branch_target = function
  | Item10BranchZero (_, _, target)
  | Item10BranchBinary (_, _, _, target) ->
      target

let item10_is_ignorable_line line =
  let s = trim line in
  s = "" || starts_with s "."

let item10_build_label_pos lines =
  let table = Hashtbl.create 64 in
  Array.iteri
    (fun i line ->
      if is_label line then
        Hashtbl.replace table (label_name line) i)
    lines;
  table

let rec item10_first_exec_after lines i =
  if i >= Array.length lines then None
  else if is_label lines.(i) || item10_is_ignorable_line lines.(i) then
    item10_first_exec_after lines (i + 1)
  else
    Some i

type item10_target_resolution =
  | Item10TargetRet
  | Item10TargetLabel of string

let item10_resolve_target lines label_pos original =
  let rec loop visited label =
    if List.mem label visited then Item10TargetLabel original
    else
      match Hashtbl.find_opt label_pos label with
      | None -> Item10TargetLabel label
      | Some pos -> (
          match item10_first_exec_after lines (pos + 1) with
          | Some instr_pos -> (
              match split_asm_words lines.(instr_pos) with
              | [ "ret" ] -> Item10TargetRet
              | [ "j"; next ] ->
                  loop (label :: visited) next
              | _ -> Item10TargetLabel label)
          | None -> Item10TargetLabel label)
  in
  loop [] original

let item10_branch_target_is_next lines label_pos i target =
  match Hashtbl.find_opt label_pos target with
  | Some target_pos when target_pos > i ->
      let rec only_ignorable j =
        if j >= target_pos then true
        else if is_label lines.(j) || item10_is_ignorable_line lines.(j) then
          only_ignorable (j + 1)
        else
          false
      in
      only_ignorable (i + 1)
  | Some _ | None -> false

let item10_constant_branch branch =
  match branch with
  | Item10BranchZero ("beqz", "x0", target) ->
      Some (Some (Printf.sprintf "    j %s" target))
  | Item10BranchZero ("bnez", "x0", _) ->
      Some None
  | Item10BranchZero _ ->
      None
  | Item10BranchBinary (opcode, lhs, rhs, target)
    when lhs = rhs ->
      begin
        match opcode with
        | "beq" | "bge" | "bgeu" ->
            Some (Some (Printf.sprintf "    j %s" target))
        | "bne" | "blt" | "bltu" ->
            Some None
        | _ ->
            None
      end
  | Item10BranchBinary _ ->
      None

let item10_can_drop_value_after live_out index reg consumer_line =
  let _, defs = uses_defs consumer_line in
  RegSet.mem reg defs || not (RegSet.mem reg live_out.(index))

let item10_rewrite_zero_consumer reg line =
  match split_asm_words line with
  | [ (("add" | "sub" | "mul" | "div" | "rem" | "slt" | "sltu" | "xor") as op);
      dst; lhs; rhs ] ->
      let lhs' = if lhs = reg then "x0" else lhs in
      let rhs' = if rhs = reg then "x0" else rhs in
      if lhs' = lhs && rhs' = rhs then None
      else Some (Printf.sprintf "    %s %s, %s, %s" op dst lhs' rhs')
  | [ (("addi" | "slti" | "sltiu" | "slli" | "srli" | "srai"
        | "andi" | "xori") as op);
      dst; src; imm ] ->
      if src = reg then
        Some (Printf.sprintf "    %s %s, x0, %s" op dst imm)
      else None
  | [ "neg"; dst; src ] ->
      if src = reg then Some (Printf.sprintf "    neg %s, x0" dst) else None
  | [ "lw"; dst; off; base ] ->
      if base = reg then
        Some (Printf.sprintf "    lw %s, %s(x0)" dst off)
      else None
  | [ "sw"; src; middle; base ] ->
      let src' = if src = reg then "x0" else src in
      let base' =
        if is_int64_literal middle && base = reg then "x0" else base
      in
      if src' = src && base' = base then None
      else if is_int64_literal middle then
        Some (Printf.sprintf "    sw %s, %s(%s)" src' middle base')
      else
        (* GNU symbol-form store: third register is a scratch/clobber, not use. *)
        Some (Printf.sprintf "    sw %s, %s, %s" src' middle base)
  | [ (("beqz" | "bnez") as op); src; target ] ->
      if src = reg then
        Some (Printf.sprintf "    %s x0, %s" op target)
      else None
  | [ (("beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu") as op);
      lhs; rhs; target ] ->
      let lhs' = if lhs = reg then "x0" else lhs in
      let rhs' = if rhs = reg then "x0" else rhs in
      if lhs' = lhs && rhs' = rhs then None
      else Some (Printf.sprintf "    %s %s, %s, %s" op lhs' rhs' target)
  | _ ->
      None

let item10_li_consumer_fold live_out second_index li_reg imm consumer =
  let can_drop =
    item10_can_drop_value_after live_out second_index li_reg consumer
  in
  if not can_drop then None
  else
    match split_asm_words consumer with
    | [ "add"; dst; lhs; rhs ]
      when fits_simm12 imm && lhs = li_reg && rhs <> li_reg ->
        Some (addi_line dst rhs imm)
    | [ "add"; dst; lhs; rhs ]
      when fits_simm12 imm && rhs = li_reg && lhs <> li_reg ->
        Some (addi_line dst lhs imm)
    | [ "sub"; dst; lhs; rhs ]
      when rhs = li_reg
           && lhs <> li_reg
           && fits_simm12 (Int64.neg imm) ->
        Some (addi_line dst lhs (Int64.neg imm))
    | [ "slt"; dst; lhs; rhs ]
      when rhs = li_reg
           && lhs <> li_reg
           && fits_simm12 imm ->
        Some (Printf.sprintf "    slti %s, %s, %Ld" dst lhs imm)
    | [ "mul"; dst; lhs; rhs ]
      when lhs = li_reg && rhs <> li_reg ->
        begin
          match item10_positive_pow2_shift imm with
          | Some shift when shift >= 1 && shift <= 31 ->
              Some (Printf.sprintf "    slli %s, %s, %d" dst rhs shift)
          | Some _ | None -> None
        end
    | [ "mul"; dst; lhs; rhs ]
      when rhs = li_reg && lhs <> li_reg ->
        begin
          match item10_positive_pow2_shift imm with
          | Some shift when shift >= 1 && shift <= 31 ->
              Some (Printf.sprintf "    slli %s, %s, %d" dst lhs shift)
          | Some _ | None -> None
        end
    | _ when imm = 0L ->
        item10_rewrite_zero_consumer li_reg consumer
    | _ ->
        None

let item10_pair_compare_branch live_out second_index first second =
  match split_asm_words first, item10_parse_branch second with
  | [ "sub"; dst; lhs; rhs ],
    Some (Item10BranchZero (branch_op, cond, target))
    when dst = cond && not (RegSet.mem dst live_out.(second_index)) ->
      let op = if branch_op = "bnez" then "bne" else "beq" in
      Some (Printf.sprintf "    %s %s, %s, %s" op lhs rhs target)
  | [ "sltu"; dst; "x0"; src ],
    Some (Item10BranchZero (branch_op, cond, target))
    when dst = cond && not (RegSet.mem dst live_out.(second_index)) ->
      let op = if branch_op = "bnez" then "bnez" else "beqz" in
      Some (Printf.sprintf "    %s %s, %s" op src target)
  | [ (("slt" | "sltu") as cmp); dst; lhs; rhs ],
    Some (Item10BranchZero (branch_op, cond, target))
    when dst = cond && not (RegSet.mem dst live_out.(second_index)) ->
      let op =
        match cmp, branch_op with
        | "slt", "bnez" -> "blt"
        | "slt", "beqz" -> "bge"
        | "sltu", "bnez" -> "bltu"
        | "sltu", "beqz" -> "bgeu"
        | _ -> assert false
      in
      Some (Printf.sprintf "    %s %s, %s, %s" op lhs rhs target)
  | [ "sltiu"; dst; src; "1" ],
    Some (Item10BranchZero (branch_op, cond, target))
    when dst = cond && not (RegSet.mem dst live_out.(second_index)) ->
      let op = if branch_op = "bnez" then "beqz" else "bnez" in
      Some (Printf.sprintf "    %s %s, %s" op src target)
  | _ ->
      None

let item10_triple_compare_branch live_out third_index first second third =
  match split_asm_words first,
        split_asm_words second,
        item10_parse_branch third with
  | [ "slt"; mid; lhs; rhs ],
    [ "xori"; dst; src; "1" ],
    Some (Item10BranchZero (branch_op, cond, target))
    when src = mid
         && dst = cond
         && not (RegSet.mem mid live_out.(third_index))
         && not (RegSet.mem dst live_out.(third_index)) ->
      let op = if branch_op = "bnez" then "bge" else "blt" in
      Some (Printf.sprintf "    %s %s, %s, %s" op lhs rhs target)
  | [ "sltu"; mid; lhs; rhs ],
    [ "xori"; dst; src; "1" ],
    Some (Item10BranchZero (branch_op, cond, target))
    when src = mid
         && dst = cond
         && not (RegSet.mem mid live_out.(third_index))
         && not (RegSet.mem dst live_out.(third_index)) ->
      let op = if branch_op = "bnez" then "bgeu" else "bltu" in
      Some (Printf.sprintf "    %s %s, %s, %s" op lhs rhs target)
  | [ "sub"; mid; lhs; rhs ],
    [ "sltiu"; dst; src; "1" ],
    Some (Item10BranchZero (branch_op, cond, target))
    when src = mid
         && dst = cond
         && not (RegSet.mem mid live_out.(third_index))
         && not (RegSet.mem dst live_out.(third_index)) ->
      let op = if branch_op = "bnez" then "beq" else "bne" in
      Some (Printf.sprintf "    %s %s, %s, %s" op lhs rhs target)
  | [ "sub"; mid; lhs; rhs ],
    [ "sltu"; dst; "x0"; src ],
    Some (Item10BranchZero (branch_op, cond, target))
    when src = mid
         && dst = cond
         && not (RegSet.mem mid live_out.(third_index))
         && not (RegSet.mem dst live_out.(third_index)) ->
      let op = if branch_op = "bnez" then "bne" else "beq" in
      Some (Printf.sprintf "    %s %s, %s, %s" op lhs rhs target)
  | _ ->
      None


(* -------------------------------------------------------------------------- *)
(* Post-RA copy-back folding.                                                 *)
(*                                                                            *)
(* Recognize a pure value update that is first computed into a temporary and  *)
(* only copied back to the original register later in the same straight-line  *)
(* region:                                                                    *)
(*                                                                            *)
(*     addi tmp, base, K                                                      *)
(*       ... may read base, but must not write base or touch tmp ...          *)
(*     addi base, tmp, 0                                                      *)
(*                                                                            *)
(* and sink the computation to the copy-back site:                            *)
(*                                                                            *)
(*       ...                                                                  *)
(*     addi base, base, K                                                      *)
(*                                                                            *)
(* This preserves all intervening reads of the old [base] value and removes   *)
(* one physical-register copy.  We deliberately stop at every CFG/call        *)
(* boundary and only accept instructions whose register effects are known.    *)
(* -------------------------------------------------------------------------- *)

let item10_copy_back_enabled () =
  Sys.getenv_opt "TOYC_DISABLE_ITEM10_COPY_BACK" = None

let item10_copy_back_debug_enabled () =
  Sys.getenv_opt "TOYC_DEBUG_ASM_COPY_BACK" <> None

let item10_copy_back_middle_opcode_safe = function
  | "li" | "la" | "lw" | "sw"
  | "addi" | "add" | "sub" | "mul" | "div" | "rem"
  | "slt" | "sltu" | "slti" | "sltiu"
  | "slli" | "srli" | "srai"
  | "andi" | "xor" | "xori" | "neg" ->
      true
  | _ ->
      false

let item10_copy_back_barrier line =
  let s = trim line in
  if s = "" then false
  else if is_label line || starts_with s "." then true
  else
    match split_asm_words line with
    | [] -> false
    | opcode :: _ -> not (item10_copy_back_middle_opcode_safe opcode)

let item10_copy_back_fold_pass asm =
  if not (item10_copy_back_enabled ()) then asm
  else
    let lines = asm |> split_lines |> Array.of_list in
    let n = Array.length lines in
    let live_out = compute_live_out lines in
    let removed = Array.make n false in
    let replacements : string option array = Array.make n None in
    let folds = ref 0 in

    let effective_line i =
      match replacements.(i) with
      | Some line -> line
      | None -> lines.(i)
    in

    let rec find_copy_back tmp base imm j =
      if j >= n then None
      else if removed.(j) then find_copy_back tmp base imm (j + 1)
      else
        let line = effective_line j in
        if item10_copy_back_barrier line then None
        else
          match parse_move line with
          | Some (dst, src)
            when dst = base
                 && src = tmp
                 && not (RegSet.mem tmp live_out.(j)) ->
              Some j
          | Some (dst, src) when dst = base && src = tmp ->
              (* [tmp] remains live after the copy-back, so deleting the
                 producer would destroy a later use of its value. *)
              None
          | _ ->
              let uses, defs = uses_defs line in
              (* [tmp] must remain a private carrier until the copy-back. *)
              if RegSet.mem tmp uses || RegSet.mem tmp defs then None
              (* The old [base] value may be read, but must not be overwritten
                 before the delayed update is installed. *)
              else if RegSet.mem base defs then None
              else find_copy_back tmp base imm (j + 1)
    in

    for i = 0 to n - 1 do
      if not removed.(i) && replacements.(i) = None then
        match parse_addi lines.(i) with
        | Some (tmp, base, imm)
          when tmp <> base
               && imm <> 0L
               && value_register tmp
               && value_register base ->
            begin
              match find_copy_back tmp base imm (i + 1) with
              | Some j ->
                  removed.(i) <- true;
                  replacements.(j) <- Some (addi_line base base imm);
                  incr folds;
                  if item10_copy_back_debug_enabled () then
                    Printf.eprintf
                      "asm-copy-back producer=%d copy=%d tmp=%s base=%s imm=%Ld\n%!"
                      (i + 1) (j + 1) tmp base imm
              | None ->
                  ()
            end
        | Some _ | None ->
            ()
    done;

    if !folds = 0 then asm
    else
      let out = ref [] in
      for i = n - 1 downto 0 do
        if not removed.(i) then
          out := effective_line i :: !out
      done;
      String.concat "\n" !out ^ "\n"

let item10_final_asm_cleanup_pass asm =
  if not (item10_final_asm_cleanup_enabled ()) then asm
  else
    let lines = asm |> split_lines |> Array.of_list in
    let n = Array.length lines in
    let live_out = compute_live_out lines in
    let label_pos = item10_build_label_pos lines in
    let rec loop i acc =
      if i >= n then List.rev acc
      else if i + 2 < n then
        begin
          match item10_triple_compare_branch
                  live_out (i + 2)
                  lines.(i) lines.(i + 1) lines.(i + 2) with
          | Some replacement ->
              loop (i + 3) (replacement :: acc)
          | None ->
              loop_pair i acc
        end
      else
        loop_pair i acc

    and loop_pair i acc =
      if i + 1 < n then
        begin
          match item10_pair_compare_branch
                  live_out (i + 1) lines.(i) lines.(i + 1) with
          | Some replacement ->
              loop (i + 2) (replacement :: acc)
          | None ->
              begin
                match parse_move lines.(i), item10_parse_branch lines.(i + 1) with
                | Some (dst, src), Some branch
                  when dst <> src
                       && not (RegSet.mem dst live_out.(i + 1)) ->
                    let branch' = item10_replace_branch_reg branch dst src in
                    if branch' <> branch then begin
                      loop (i + 2) (item10_branch_line branch' :: acc)
                    end
                    else
                      loop_li_pair i acc
                | _ ->
                    loop_li_pair i acc
              end
        end
      else
        loop_single i acc

    and loop_li_pair i acc =
      if i + 1 < n then
        begin
          match item10_parse_li lines.(i) with
          | Some (reg, imm) ->
              begin
                match item10_li_consumer_fold
                        live_out (i + 1) reg imm lines.(i + 1) with
                | Some replacement ->
                    loop (i + 2) (replacement :: acc)
                | None ->
                    loop_single i acc
              end
          | None ->
              loop_single i acc
        end
      else
        loop_single i acc

    and loop_single i acc =
      let line = lines.(i) in
      match item10_parse_branch line with
      | Some branch ->
          begin
            match item10_constant_branch branch with
            | Some None ->
                loop (i + 1) acc
            | Some (Some replacement) ->
                loop (i + 1) (replacement :: acc)
            | None ->
                let target = item10_branch_target branch in
                if item10_branch_target_is_next lines label_pos i target then begin
                  loop (i + 1) acc
                end
                else
                  begin
                    match item10_resolve_target lines label_pos target with
                    | Item10TargetLabel final_target
                      when final_target <> target ->
                        let branch' =
                          item10_replace_branch_target branch final_target
                        in
                        loop (i + 1) (item10_branch_line branch' :: acc)
                    | Item10TargetRet
                    | Item10TargetLabel _ ->
                        loop (i + 1) (line :: acc)
                  end
          end
      | None ->
          begin
            match split_asm_words line with
            | [ "j"; target ] ->
                begin
                  match item10_resolve_target lines label_pos target with
                  | Item10TargetRet ->
                      loop (i + 1) ("    ret" :: acc)
                  | Item10TargetLabel final_target
                    when final_target <> target ->
                      loop
                        (i + 1)
                        (Printf.sprintf "    j %s" final_target :: acc)
                  | Item10TargetLabel _ ->
                      loop (i + 1) (line :: acc)
                end
            | _ ->
                loop (i + 1) (line :: acc)
          end
    in

    let result = String.concat "\n" (loop 0 []) ^ "\n" in
    result

let peephole asm =
  let rec fix current =
    let next =
      current
      |> peephole_pass
      |> item10_copy_back_fold_pass
      |> item10_final_asm_cleanup_pass
    in
    if next = current then current else fix next
  in
  fix asm
