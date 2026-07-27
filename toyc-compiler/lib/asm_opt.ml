let trim = String.trim

let starts_with s prefix =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix

let split_ws s =
  s |> trim |> String.split_on_char ' ' |> List.filter (fun p -> p <> "")

let parse_push l1 l2 =
  match (split_ws l1, split_ws l2) with
  | [ "addi"; "sp,"; "sp,"; "-4" ], [ "sw"; reg_comma; "0(sp)" ] ->
      Some (String.sub reg_comma 0 (String.length reg_comma - 1))
  | _ -> None

let parse_pop l1 l2 =
  match (split_ws l1, split_ws l2) with
  | [ "lw"; reg_comma; "0(sp)" ], [ "addi"; "sp,"; "sp,"; "4" ] ->
      Some (String.sub reg_comma 0 (String.length reg_comma - 1))
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

let peephole asm =
  let lines = asm |> String.split_on_char '\n' |> Array.of_list in
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
    else if i + 1 < n && starts_with (trim lines.(i)) "j " && is_label lines.(i + 1)
    then
      let label = label_name lines.(i + 1) in
      if is_jump_to lines.(i) label then loop (i + 1) acc else loop (i + 1) (lines.(i) :: acc)
    else loop (i + 1) (lines.(i) :: acc)
  in
  String.concat "\n" (loop 0 []) ^ "\n"

