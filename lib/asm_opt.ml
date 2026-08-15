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

let split_lines asm =
  match List.rev (String.split_on_char '\n' asm) with
  | "" :: rest -> List.rev rest
  | rev_lines -> List.rev rev_lines

let parse_la line =
  match split_ws line with
  | [ "la"; reg_comma; label ] -> Some (strip_trailing_comma reg_comma, label)
  | _ -> None

let clears_address line =
  let line = trim line in
  is_label line
  || starts_with line "call "
  || starts_with line "j "
  || starts_with line "b"

let reuse_global_addresses asm =
  let rec loop known acc = function
    | [] -> List.rev acc
    | line :: rest -> (
        match parse_la line with
        | Some (reg, label) when known = Some (reg, label) -> loop known acc rest
        | Some addr -> loop (Some addr) (line :: acc) rest
        | None ->
            let known = if clears_address line then None else known in
            loop known (line :: acc) rest)
  in
  String.concat "\n" (loop None [] (split_lines asm)) ^ "\n"

let rec emit_opt_lines acc = function
  | [] -> acc
  | None :: rest -> emit_opt_lines acc rest
  | Some line :: rest -> emit_opt_lines (line :: acc) rest

let peephole_pass asm =
  let lines = asm |> split_lines |> Array.of_list in
  let n = Array.length lines in
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
      match (parse_move lines.(i), parse_move lines.(i + 1)) with
      | Some (dst1, src1), Some (dst2, src2) when dst1 = dst2 ->
          if src2 = dst2 then
            let acc' = emit_opt_lines acc [ move_line dst1 src1 ] in
            loop (i + 2) acc'
          else loop (i + 1) acc
      | Some (dst1, src1), Some (dst2, src2) when src2 = dst1 ->
          let acc' = emit_opt_lines acc [ move_line dst1 src1; move_line dst2 src1 ] in
          loop (i + 2) acc'
      | Some (dst, src), _ when dst = src ->
          loop (i + 1) acc
      | _ -> loop_tail i acc
    else if i + 1 < n && starts_with (trim lines.(i)) "j " && is_label lines.(i + 1)
    then
      let label = label_name lines.(i + 1) in
      if is_jump_to lines.(i) label then loop (i + 1) acc else loop (i + 1) (lines.(i) :: acc)
    else loop (i + 1) (lines.(i) :: acc)
  and loop_tail i acc =
    if i + 1 < n && starts_with (trim lines.(i)) "j " && is_label lines.(i + 1) then
      let label = label_name lines.(i + 1) in
      if is_jump_to lines.(i) label then loop (i + 1) acc else loop (i + 1) (lines.(i) :: acc)
    else loop (i + 1) (lines.(i) :: acc)
  in
  String.concat "\n" (loop 0 []) ^ "\n"

let peephole asm =
  let rec fix current =
    let next = current |> peephole_pass |> reuse_global_addresses in
    if next = current then current else fix next
  in
  fix asm
