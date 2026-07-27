open Ast

module StringMap = Map.Make (String)

type const_cell =
  | Known of int64
  | Unknown

type const_env = const_cell StringMap.t list

let truth n = n <> 0L

let bool_int b = if b then 1L else 0L

let empty_env = [ StringMap.empty ]

let push_scope env = StringMap.empty :: env

let pop_scope = function
  | _ :: rest -> rest
  | [] -> []

let add_binding env name value =
  match env with
  | scope :: rest -> StringMap.add name value scope :: rest
  | [] -> [ StringMap.singleton name value ]

let add_const env name value = add_binding env name (Known value)

let add_shadow env name = add_binding env name Unknown

let find_const env name =
  let rec loop = function
    | [] -> None
    | scope :: rest -> (
        match StringMap.find_opt name scope with
        | Some (Known v) -> Some v
        | Some Unknown -> None
        | None -> loop rest)
  in
  loop env

let fold_binop op a b =
  match op with
  | Add -> Some Int64.(add a b)
  | Sub -> Some Int64.(sub a b)
  | Mul -> Some Int64.(mul a b)
  | Div -> if b = 0L then None else Some Int64.(div a b)
  | Mod -> if b = 0L then None else Some Int64.(rem a b)
  | Lt -> Some (bool_int (a < b))
  | Gt -> Some (bool_int (a > b))
  | Le -> Some (bool_int (a <= b))
  | Ge -> Some (bool_int (a >= b))
  | Eq -> Some (bool_int (a = b))
  | Ne -> Some (bool_int (a <> b))
  | LAnd -> Some (bool_int (truth a && truth b))
  | LOr -> Some (bool_int (truth a || truth b))

let rec fold_expr env = function
  | Int _ as e -> e
  | Var name -> (
      match find_const env name with
      | Some v -> Int v
      | None -> Var name)
  | Call (name, args) -> Call (name, List.map (fold_expr env) args)
  | Unary (op, e) -> (
      let e' = fold_expr env e in
      match (op, e') with
      | UPlus, Int v -> Int v
      | UMinus, Int v -> Int (Int64.neg v)
      | UNot, Int v -> Int (bool_int (not (truth v)))
      | _ -> Unary (op, e'))
  | Binary (LAnd, a, b) -> (
      let a' = fold_expr env a in
      match a' with
      | Int 0L -> Int 0L
      | Int _ -> (
          match fold_expr env b with
          | Int v -> Int (bool_int (truth v))
          | b' -> Binary (LAnd, a', b'))
      | _ -> Binary (LAnd, a', fold_expr env b))
  | Binary (LOr, a, b) -> (
      let a' = fold_expr env a in
      match a' with
      | Int v when truth v -> Int 1L
      | Int _ -> (
          match fold_expr env b with
          | Int v -> Int (bool_int (truth v))
          | b' -> Binary (LOr, a', b'))
      | _ -> Binary (LOr, a', fold_expr env b))
  | Binary (op, a, b) -> (
      let a' = fold_expr env a in
      let b' = fold_expr env b in
      match (a', b') with
      | Int av, Int bv -> (
          match fold_binop op av bv with
          | Some v -> Int v
          | None -> Binary (op, a', b'))
      | _ -> Binary (op, a', b'))

let const_of_expr = function
  | Int v -> Some v
  | _ -> None

let rec terminates = function
  | Return _ | Break | Continue -> true
  | Block stmts -> List.exists terminates stmts
  | If (_, t, Some e) -> terminates t && terminates e
  | _ -> false

let fold_decl env d =
  let init = fold_expr env d.init in
  let env' =
    if d.is_const then
      match const_of_expr init with
      | Some v -> add_const env d.ident.name v
      | None -> add_shadow env d.ident.name
    else add_shadow env d.ident.name
  in
  ({ d with init }, env')

let rec fold_stmt env = function
  | Block stmts ->
      let stmts', _ = fold_stmt_list (push_scope env) stmts in
      (Block stmts', env)
  | Empty -> (Empty, env)
  | Expr e -> (Expr (fold_expr env e), env)
  | Assign (name, e) -> (Assign (name, fold_expr env e), env)
  | Decl d ->
      let d', env' = fold_decl env d in
      (Decl d', env')
  | If (cond, t, e) -> (
      match fold_expr env cond with
      | Int v when truth v ->
          let t', _ = fold_stmt env t in
          (t', env)
      | Int _ -> (
          match e with
          | None -> (Empty, env)
          | Some else_s ->
              let else_s', _ = fold_stmt env else_s in
              (else_s', env))
      | cond' ->
          let t', _ = fold_stmt env t in
          let e' = Option.map (fun s -> fst (fold_stmt env s)) e in
          (If (cond', t', e'), env))
  | While (cond, body) -> (
      match fold_expr env cond with
      | Int 0L -> (Empty, env)
      | cond' ->
          let body', _ = fold_stmt env body in
          (While (cond', body'), env))
  | Break -> (Break, env)
  | Continue -> (Continue, env)
  | Return e -> (Return (Option.map (fold_expr env) e), env)

and fold_stmt_list env stmts =
  let rec loop env acc = function
    | [] -> (List.rev acc, env)
    | s :: rest ->
        let s', env' = fold_stmt env s in
        let acc' = s' :: acc in
        if terminates s' then (List.rev acc', env') else loop env' acc' rest
  in
  loop env [] stmts

let optimize_ast program =
  let rec loop env acc = function
    | [] -> List.rev acc
    | TopDecl d :: rest ->
        let d', env' = fold_decl env d in
        loop env' (TopDecl d' :: acc) rest
    | FuncDef f :: rest ->
        let params_shadow_consts =
          List.fold_left
            (fun env (p : Ast.ident) -> add_shadow env p.name)
            (push_scope env) f.params
        in
        let body, _ = fold_stmt_list params_shadow_consts f.body in
        loop env (FuncDef { f with body } :: acc) rest
  in
  loop empty_env [] program

let optimize_cfg cfg = cfg
