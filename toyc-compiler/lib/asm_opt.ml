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

let peephole asm =
  let rec fix current =
    let next = peephole_pass current in
    if next = current then current else fix next
  in
  fix asm
