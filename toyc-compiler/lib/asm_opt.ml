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
          | "slt" | "sltu" | "sltiu" | "xori" | "neg" ->
              def_first ()
          | "sw" ->
              (operand_regs, RegSet.empty)
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

let item10_machine_mix_audit_enabled () =
  Sys.getenv_opt "TOYC_DEBUG_ITEM10_MACHINE_MIX" <> None
  && Array.exists (fun arg -> arg = "-opt") Sys.argv

let item10_is_exec_line line =
  let s = trim line in
  s <> "" && not (is_label line) && not (starts_with s ".")

let item10_next_exec_line lines start =
  let n = Array.length lines in
  let rec loop i =
    if i >= n then None
    else if item10_is_exec_line lines.(i) then Some (i, lines.(i))
    else if is_label lines.(i) then None
    else loop (i + 1)
  in
  loop start

let item10_mem_base operands =
  match operands with
  | _reg :: _off :: base :: _ -> Some base
  | _ -> None

let item10_reg_used_by_line reg line =
  let words = split_asm_words line in
  List.exists (fun w -> w = reg) words

let item10_machine_mix_audit asm =
  if item10_machine_mix_audit_enabled () then begin
    let lines = asm |> split_lines |> Array.of_list in

    let instrs = ref 0 in
    let moves = ref 0 in
    let li = ref 0 in
    let la = ref 0 in
    let lw = ref 0 in
    let sw = ref 0 in
    let stack_lw = ref 0 in
    let stack_sw = ref 0 in
    let nonstack_lw = ref 0 in
    let nonstack_sw = ref 0 in

    let la_mem_load = ref 0 in
    let la_mem_store = ref 0 in
    let la_other = ref 0 in

    let li_next_arith = ref 0 in
    let li_next_branch = ref 0 in
    let li_next_other = ref 0 in

    let addi = ref 0 in
    let add = ref 0 in
    let sub = ref 0 in
    let mul = ref 0 in
    let div = ref 0 in
    let rem = ref 0 in

    let compare_materialize = ref 0 in
    let cond_branch = ref 0 in
    let jump = ref 0 in
    let call = ref 0 in
    let ret = ref 0 in
    let other = ref 0 in

    let note_la i dst =
      match item10_next_exec_line lines (i + 1) with
      | Some (_, next_line) ->
          begin
            match split_asm_words next_line with
            | "lw" :: operands ->
                begin
                  match item10_mem_base operands with
                  | Some base when base = dst -> incr la_mem_load
                  | Some _ | None -> incr la_other
                end
            | "sw" :: operands ->
                begin
                  match item10_mem_base operands with
                  | Some base when base = dst -> incr la_mem_store
                  | Some _ | None -> incr la_other
                end
            | _ -> incr la_other
          end
      | None -> incr la_other
    in

    let note_li i dst =
      match item10_next_exec_line lines (i + 1) with
      | Some (_, next_line) when item10_reg_used_by_line dst next_line ->
          begin
            match split_asm_words next_line with
            | ("add" | "sub" | "mul" | "div" | "rem"
              | "slt" | "sltu" | "sltiu" | "xori" | "addi") :: _ ->
                incr li_next_arith
            | ("beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"
              | "beqz" | "bnez") :: _ ->
                incr li_next_branch
            | _ -> incr li_next_other
          end
      | Some _ | None ->
          incr li_next_other
    in

    Array.iteri
      (fun i line ->
        if item10_is_exec_line line then begin
          incr instrs;
          match split_asm_words line with
          | [] -> ()
          | opcode :: operands ->
              begin
                match opcode with
                | "addi" ->
                    begin
                      match operands with
                      | [ dst; src; "0" ] when dst <> src ->
                          incr moves
                      | _ ->
                          incr addi
                    end
                | "add" -> incr add
                | "sub" -> incr sub
                | "mul" -> incr mul
                | "div" -> incr div
                | "rem" -> incr rem
                | "slt" | "sltu" | "sltiu" | "xori" ->
                    incr compare_materialize
                | "lw" ->
                    incr lw;
                    begin
                      match item10_mem_base operands with
                      | Some "sp" -> incr stack_lw
                      | Some _ | None -> incr nonstack_lw
                    end
                | "sw" ->
                    incr sw;
                    begin
                      match item10_mem_base operands with
                      | Some "sp" -> incr stack_sw
                      | Some _ | None -> incr nonstack_sw
                    end
                | "la" ->
                    incr la;
                    begin
                      match operands with
                      | dst :: _ -> note_la i dst
                      | [] -> incr la_other
                    end
                | "li" ->
                    incr li;
                    begin
                      match operands with
                      | dst :: _ -> note_li i dst
                      | [] -> incr li_next_other
                    end
                | "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"
                | "beqz" | "bnez" ->
                    incr cond_branch
                | "j" -> incr jump
                | "call" -> incr call
                | "ret" -> incr ret
                | _ -> incr other
              end
        end)
      lines;

    Printf.eprintf
      "item10-machine-mix instrs=%d moves=%d li=%d la=%d lw=%d sw=%d stack-lw=%d stack-sw=%d nonstack-lw=%d nonstack-sw=%d la-mem-load=%d la-mem-store=%d la-other=%d li-next-arith=%d li-next-branch=%d li-next-other=%d addi=%d add=%d sub=%d mul=%d div=%d rem=%d compare-materialize=%d cond-branch=%d jump=%d call=%d ret=%d other=%d asm-bytes=%d\n%!"
      !instrs !moves !li !la !lw !sw !stack_lw !stack_sw
      !nonstack_lw !nonstack_sw !la_mem_load !la_mem_store !la_other
      !li_next_arith !li_next_branch !li_next_other !addi !add !sub
      !mul !div !rem !compare_materialize !cond_branch !jump !call !ret
      !other (String.length asm)
  end

let item10_immediate_audit_enabled () =
  Sys.getenv_opt "TOYC_DEBUG_ITEM10_IMMEDIATE_AUDIT" <> None
  && Array.exists (fun arg -> arg = "-opt") Sys.argv

let item10_parse_i64 s =
  try Some (Int64.of_string s) with _ -> None

let item10_fits_simm12_i64 n =
  Int64.compare n (-2048L) >= 0 && Int64.compare n 2047L <= 0

let item10_is_positive_pow2 n =
  Int64.compare n 0L > 0
  && Int64.logand n (Int64.sub n 1L) = 0L

let item10_immediate_audit asm =
  if item10_immediate_audit_enabled () then begin
    let lines = asm |> split_lines |> Array.of_list in

    let total = ref 0 in
    let parseable = ref 0 in
    let zero = ref 0 in
    let one = ref 0 in
    let minus_one = ref 0 in
    let simm12 = ref 0 in
    let neg_fits_simm12 = ref 0 in
    let pos_pow2 = ref 0 in

    let to_add = ref 0 in
    let to_sub = ref 0 in
    let to_mul = ref 0 in
    let to_div = ref 0 in
    let to_rem = ref 0 in
    let to_slt = ref 0 in
    let to_sltu = ref 0 in
    let to_sltiu = ref 0 in
    let to_xori = ref 0 in
    let to_addi = ref 0 in
    let to_branch = ref 0 in
    let to_lw = ref 0 in
    let to_sw = ref 0 in
    let to_call = ref 0 in
    let to_move = ref 0 in
    let to_other = ref 0 in
    let no_direct_use = ref 0 in

    let mul_pow2 = ref 0 in
    let mul_simm12 = ref 0 in
    let div_pow2 = ref 0 in
    let rem_pow2 = ref 0 in
    let branch_simm12 = ref 0 in
    let compare_simm12 = ref 0 in

    Array.iteri
      (fun i line ->
        match split_asm_words line with
        | [ "li"; dst; imm_text ] ->
            incr total;
            let imm = item10_parse_i64 imm_text in
            begin
              match imm with
              | Some n ->
                  incr parseable;
                  if n = 0L then incr zero;
                  if n = 1L then incr one;
                  if n = -1L then incr minus_one;
                  if item10_fits_simm12_i64 n then incr simm12;
                  if item10_fits_simm12_i64 (Int64.neg n) then incr neg_fits_simm12;
                  if item10_is_positive_pow2 n then incr pos_pow2
              | None -> ()
            end;

            begin
              match item10_next_exec_line lines (i + 1) with
              | Some (_, next_line) when item10_reg_used_by_line dst next_line ->
                  begin
                    match split_asm_words next_line with
                    | "add" :: _ -> incr to_add
                    | "sub" :: _ -> incr to_sub
                    | "mul" :: _ ->
                        incr to_mul;
                        begin match imm with
                        | Some n when item10_is_positive_pow2 n -> incr mul_pow2
                        | _ -> ()
                        end;
                        begin match imm with
                        | Some n when item10_fits_simm12_i64 n -> incr mul_simm12
                        | _ -> ()
                        end
                    | "div" :: _ ->
                        incr to_div;
                        begin match imm with
                        | Some n when item10_is_positive_pow2 n -> incr div_pow2
                        | _ -> ()
                        end
                    | "rem" :: _ ->
                        incr to_rem;
                        begin match imm with
                        | Some n when item10_is_positive_pow2 n -> incr rem_pow2
                        | _ -> ()
                        end
                    | "slt" :: _ ->
                        incr to_slt;
                        begin match imm with
                        | Some n when item10_fits_simm12_i64 n -> incr compare_simm12
                        | _ -> ()
                        end
                    | "sltu" :: _ ->
                        incr to_sltu;
                        begin match imm with
                        | Some n when item10_fits_simm12_i64 n -> incr compare_simm12
                        | _ -> ()
                        end
                    | "sltiu" :: _ -> incr to_sltiu
                    | "xori" :: _ -> incr to_xori
                    | "addi" :: _ ->
                        begin
                          match parse_move next_line with
                          | Some _ -> incr to_move
                          | None -> incr to_addi
                        end
                    | ("beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"
                      | "beqz" | "bnez") :: _ ->
                        incr to_branch;
                        begin match imm with
                        | Some n when item10_fits_simm12_i64 n -> incr branch_simm12
                        | _ -> ()
                        end
                    | "lw" :: _ -> incr to_lw
                    | "sw" :: _ -> incr to_sw
                    | "call" :: _ -> incr to_call
                    | _ -> incr to_other
                  end
              | Some _ | None -> incr no_direct_use
            end
        | _ -> ())
      lines;

    Printf.eprintf
      "item10-immediate-audit total=%d parseable=%d zero=%d one=%d minus-one=%d simm12=%d neg-fits-simm12=%d pos-pow2=%d to-add=%d to-sub=%d to-mul=%d to-div=%d to-rem=%d to-slt=%d to-sltu=%d to-sltiu=%d to-xori=%d to-addi=%d to-branch=%d to-lw=%d to-sw=%d to-call=%d to-move=%d to-other=%d no-direct-use=%d mul-pow2=%d mul-simm12=%d div-pow2=%d rem-pow2=%d branch-simm12=%d compare-simm12=%d\n%!"
      !total !parseable !zero !one !minus_one !simm12 !neg_fits_simm12
      !pos_pow2 !to_add !to_sub !to_mul !to_div !to_rem !to_slt !to_sltu
      !to_sltiu !to_xori !to_addi !to_branch !to_lw !to_sw !to_call
      !to_move !to_other !no_direct_use !mul_pow2 !mul_simm12 !div_pow2
      !rem_pow2 !branch_simm12 !compare_simm12
  end

let peephole asm =
  let rec fix current =
    let next = peephole_pass current in
    if next = current then current else fix next
  in
  let result = fix asm in
  item10_machine_mix_audit result;
  item10_immediate_audit result;
  result
