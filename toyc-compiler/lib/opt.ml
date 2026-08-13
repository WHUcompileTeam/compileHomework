open Ast

module StringMap = Map.Make (String)
module LabelSet = Set.Make (String)
module IntSet = Set.Make (Int)

module PlaceOrd = struct
  type t = Tcg.place

  let compare = Stdlib.compare
end

module PlaceSet = Set.Make (PlaceOrd)
module PlaceMap = Map.Make (PlaceOrd)
module IntMap = Map.Make (Int)

module InstrKeyOrd = struct
  type t = string * int

  let compare = Stdlib.compare
end

module InstrKeySet = Set.Make (InstrKeyOrd)

type const_cell =
  | Known of int64
  | Unknown

type const_env = const_cell StringMap.t list

type inline_func = {
  params : string list;
  body_stmts : stmt list;
  cost : int;
  param_uses : int StringMap.t;
}

let truth n = n <> 0L

let bool_int b = if b then 1L else 0L

let int32_modulus = 0x1_0000_0000L
let int32_sign_bit = 0x8000_0000L
let int32_mask = 0xFFFF_FFFFL

let i32 value =
  let masked = Int64.logand value int32_mask in
  if masked >= int32_sign_bit then Int64.sub masked int32_modulus else masked

let has_prefix prefix text =
  let prefix_len = String.length prefix in
  String.length text >= prefix_len && String.sub text 0 prefix_len = prefix

let empty_env = [ StringMap.empty ]

let push_scope env = StringMap.empty :: env

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
  let a = i32 a in
  let b = i32 b in
  match op with
  | Add -> Some (i32 Int64.(add a b))
  | Sub -> Some (i32 Int64.(sub a b))
  | Mul -> Some (i32 Int64.(mul a b))
  | Div -> if b = 0L then None else Some (i32 Int64.(div a b))
  | Mod -> if b = 0L then None else Some (i32 Int64.(rem a b))
  | Lt -> Some (bool_int (a < b))
  | Gt -> Some (bool_int (a > b))
  | Le -> Some (bool_int (a <= b))
  | Ge -> Some (bool_int (a >= b))
  | Eq -> Some (bool_int (a = b))
  | Ne -> Some (bool_int (a <> b))
  | LAnd -> Some (bool_int (truth a && truth b))
  | LOr -> Some (bool_int (truth a || truth b))

let rec expr_has_call = function
  | Int _ | Var _ -> false
  | Call _ -> true
  | Unary (_, e) -> expr_has_call e
  | Binary (_, lhs, rhs) -> expr_has_call lhs || expr_has_call rhs

let expr_is_pure expr = not (expr_has_call expr)

let rec expr_cost = function
  | Int _ | Var _ -> 1
  | Call (_, args) ->
      1 + List.fold_left (fun acc arg -> acc + expr_cost arg) 0 args
  | Unary (_, e) -> 1 + expr_cost e
  | Binary (_, lhs, rhs) -> 1 + expr_cost lhs + expr_cost rhs

let rec expr_var_uses counts = function
  | Int _ -> counts
  | Var name ->
      let count = Option.value ~default:0 (StringMap.find_opt name counts) in
      StringMap.add name (count + 1) counts
  | Call (_, args) -> List.fold_left expr_var_uses counts args
  | Unary (_, e) -> expr_var_uses counts e
  | Binary (_, lhs, rhs) -> expr_var_uses (expr_var_uses counts lhs) rhs

let rec stmt_cost = function
  | Block stmts -> 1 + List.fold_left (fun acc stmt -> acc + stmt_cost stmt) 0 stmts
  | Empty -> 0
  | Expr expr -> 1 + expr_cost expr
  | Assign (_, expr) -> 1 + expr_cost expr
  | Decl d -> 1 + expr_cost d.init
  | If (cond, t, e) ->
      let else_cost =
        match e with
        | Some else_stmt -> stmt_cost else_stmt
        | None -> 0
      in
      1 + expr_cost cond + stmt_cost t + else_cost
  | While (cond, body) -> 1 + expr_cost cond + stmt_cost body
  | Break | Continue -> 1
  | Return None -> 1
  | Return (Some expr) -> 1 + expr_cost expr

let rec stmt_var_uses counts = function
  | Block stmts -> List.fold_left stmt_var_uses counts stmts
  | Empty | Break | Continue | Return None -> counts
  | Expr expr -> expr_var_uses counts expr
  | Assign (_, expr) -> expr_var_uses counts expr
  | Decl d -> expr_var_uses counts d.init
  | If (cond, t, e) ->
      let counts = expr_var_uses counts cond in
      let counts = stmt_var_uses counts t in
      begin
        match e with
        | Some else_stmt -> stmt_var_uses counts else_stmt
        | None -> counts
      end
  | While (cond, body) -> stmt_var_uses (expr_var_uses counts cond) body
  | Return (Some expr) -> expr_var_uses counts expr

let stmt_list_cost stmts =
  List.fold_left (fun acc stmt -> acc + stmt_cost stmt) 0 stmts

let stmt_list_var_uses counts stmts =
  List.fold_left stmt_var_uses counts stmts

let rec inline_stmt_template_supported = function
  | Block stmts -> List.for_all inline_stmt_template_supported stmts
  | Empty -> true
  | Expr _ | Assign _ | Decl _ | Return (Some _) -> true
  | If (_, t, e) ->
      let else_supported =
        match e with
        | Some else_stmt -> inline_stmt_template_supported else_stmt
        | None -> true
      in
      inline_stmt_template_supported t && else_supported
  | While _ | Break | Continue -> false
  | Return None -> false

let inline_expr_limit = 28
let inline_expr_depth_limit = 6

type inline_scope_env = expr StringMap.t list

type inline_stmt_result =
  | InlineContinue of inline_scope_env
  | InlineReturn of expr

let empty_inline_scope = [ StringMap.empty ]

let push_inline_scope env = StringMap.empty :: env

let pop_inline_scope = function
  | _ :: rest -> rest
  | [] -> []

let add_inline_binding env name value =
  match env with
  | scope :: rest -> StringMap.add name value scope :: rest
  | [] -> [ StringMap.singleton name value ]

let rec find_inline_binding env name =
  match env with
  | [] -> None
  | scope :: rest -> (
      match StringMap.find_opt name scope with
      | Some value -> Some value
      | None -> find_inline_binding rest name)

let rec set_inline_binding env name value =
  match env with
  | [] -> None
  | scope :: rest ->
      if StringMap.mem name scope then Some (StringMap.add name value scope :: rest)
      else Option.map (fun rest -> scope :: rest) (set_inline_binding rest name value)

let rec subst_inline_expr_scoped env = function
  | Int _ as e -> e
  | Var name -> (
      match find_inline_binding env name with
      | Some value -> value
      | None -> Var name)
  | Call (name, args) -> Call (name, List.map (subst_inline_expr_scoped env) args)
  | Unary (op, e) -> Unary (op, subst_inline_expr_scoped env e)
  | Binary (op, lhs, rhs) ->
      Binary (op, subst_inline_expr_scoped env lhs, subst_inline_expr_scoped env rhs)

let rec inline_expr func_env depth = function
  | Int _ as e -> e
  | Var _ as e -> e
  | Call (name, args) ->
      let args = List.map (inline_expr func_env depth) args in
      if depth = 0 then Call (name, args)
      else
        (match StringMap.find_opt name func_env with
        | Some def
          when List.length def.params = List.length args
               && List.for_all2
                    (fun param arg ->
                      let uses = Option.value ~default:0 (StringMap.find_opt param def.param_uses) in
                      not (expr_has_call arg) || uses <= 1)
                    def.params args ->
             let subst_scope =
               List.fold_left2
                 (fun env param arg -> add_inline_binding env param arg)
                 empty_inline_scope def.params args
             in
            (match eval_inline_stmt_list func_env (depth - 1) subst_scope def.body_stmts with
            | Some (InlineReturn body) -> inline_expr func_env (depth - 1) body
            | Some (InlineContinue _) | None -> Call (name, args))
        | Some _ | None -> Call (name, args))
  | Unary (op, e) -> Unary (op, inline_expr func_env depth e)
  | Binary (op, lhs, rhs) ->
      Binary (op, inline_expr func_env depth lhs, inline_expr func_env depth rhs)

and inline_pure_expr_scoped func_env depth env expr =
  let expr = subst_inline_expr_scoped env expr in
  let expr = inline_expr func_env depth expr in
  if expr_has_call expr then None else Some expr

and eval_inline_stmt_list func_env depth env = function
  | [] -> Some (InlineContinue env)
  | Empty :: rest -> eval_inline_stmt_list func_env depth env rest
  | Expr expr :: rest -> (
      match inline_pure_expr_scoped func_env depth env expr with
      | Some _ -> eval_inline_stmt_list func_env depth env rest
      | None -> None)
  | Decl d :: rest -> (
      match inline_pure_expr_scoped func_env depth env d.init with
      | Some init ->
          eval_inline_stmt_list func_env depth (add_inline_binding env d.ident.name init) rest
      | None -> None)
  | Assign (name, expr) :: rest -> (
      match inline_pure_expr_scoped func_env depth env expr with
      | Some value -> (
          match set_inline_binding env name value with
          | Some env -> eval_inline_stmt_list func_env depth env rest
          | None -> None)
      | None -> None)
  | Block stmts :: rest -> (
      match eval_inline_stmt_list func_env depth (push_inline_scope env) stmts with
      | Some (InlineContinue inner_env) ->
          eval_inline_stmt_list func_env depth (pop_inline_scope inner_env) rest
      | Some (InlineReturn expr) -> Some (InlineReturn expr)
      | None -> None)
  | If (cond, then_stmt, else_stmt) :: rest -> (
      match inline_pure_expr_scoped func_env depth env cond with
      | Some (Int value) when truth value -> eval_inline_stmt_list func_env depth env (then_stmt :: rest)
      | Some (Int _) -> (
          match else_stmt with
          | Some else_stmt -> eval_inline_stmt_list func_env depth env (else_stmt :: rest)
          | None -> eval_inline_stmt_list func_env depth env rest)
      | Some _ | None -> None)
  | While _ :: _ -> None
  | Break :: _ | Continue :: _ -> None
  | Return (Some expr) :: _ ->
      Option.map (fun expr -> InlineReturn expr) (inline_pure_expr_scoped func_env depth env expr)
  | Return None :: _ -> None

let inline_def_of_func (f : Ast.func) =
  match f.ret with
  | TInt when List.for_all inline_stmt_template_supported f.body ->
      let cost = stmt_list_cost f.body in
      if cost <= inline_expr_limit then
        Some
          {
            params = List.map (fun (param : Ast.ident) -> param.name) f.params;
            body_stmts = f.body;
            cost;
            param_uses = stmt_list_var_uses StringMap.empty f.body;
          }
      else None
  | TInt | TVoid -> None

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
      | UPlus, Int v -> Int (i32 v)
      | UMinus, Int v -> Int (i32 (Int64.neg (i32 v)))
      | UNot, Int v -> Int (bool_int (not (truth (i32 v))))
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
      | _ -> (
          match op with
          | Add when a' = Int 0L -> b'
          | Add when b' = Int 0L -> a'
          | Sub when b' = Int 0L -> a'
          | Sub when expr_is_pure a' && a' = b' -> Int 0L
          | Mul when (a' = Int 0L && expr_is_pure b') || (b' = Int 0L && expr_is_pure a') ->
              Int 0L
          | Mul when a' = Int 1L -> b'
          | Mul when b' = Int 1L -> a'
          | Div when b' = Int 1L -> a'
          | Mod when b' = Int 1L && expr_is_pure a' -> Int 0L
          | Eq when expr_is_pure a' && a' = b' -> Int 1L
          | Ne when expr_is_pure a' && a' = b' -> Int 0L
          | Lt when expr_is_pure a' && a' = b' -> Int 0L
          | Gt when expr_is_pure a' && a' = b' -> Int 0L
          | Le when expr_is_pure a' && a' = b' -> Int 1L
          | Ge when expr_is_pure a' && a' = b' -> Int 1L
          | _ -> Binary (op, a', b')))

let rewrite_expr_ast func_env env expr =
  fold_expr env (inline_expr func_env inline_expr_depth_limit expr)

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

let fold_decl_with_inline func_env env d =
  let init = rewrite_expr_ast func_env env d.init in
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

let build_inline_func_env program =
  List.fold_left
    (fun env -> function
      | FuncDef f -> (
          match inline_def_of_func f with
          | Some def -> StringMap.add f.name.name def env
          | None -> env)
      | TopDecl _ -> env)
    StringMap.empty program

let optimize_ast_once program =
  let base_func_env = build_inline_func_env program in
  let rec fold_stmt_inline func_env env = function
    | Block stmts ->
        let stmts', _ = fold_stmt_list_inline func_env (push_scope env) stmts in
        (Block stmts', env)
    | Empty -> (Empty, env)
    | Expr e -> (Expr (rewrite_expr_ast func_env env e), env)
    | Assign (name, e) -> (Assign (name, rewrite_expr_ast func_env env e), env)
    | Decl d ->
        let d', env' = fold_decl_with_inline func_env env d in
        (Decl d', env')
    | If (cond, t, e) -> (
        match rewrite_expr_ast func_env env cond with
        | Int v when truth v ->
            let t', _ = fold_stmt_inline func_env env t in
            (t', env)
        | Int _ -> (
            match e with
            | None -> (Empty, env)
            | Some else_s ->
                let else_s', _ = fold_stmt_inline func_env env else_s in
                (else_s', env))
        | cond' ->
            let t', _ = fold_stmt_inline func_env env t in
            let e' = Option.map (fun s -> fst (fold_stmt_inline func_env env s)) e in
            (If (cond', t', e'), env))
    | While (cond, body) -> (
        match rewrite_expr_ast func_env env cond with
        | Int 0L -> (Empty, env)
        | cond' ->
            let body', _ = fold_stmt_inline func_env env body in
            (While (cond', body'), env))
    | Break -> (Break, env)
    | Continue -> (Continue, env)
    | Return e -> (Return (Option.map (rewrite_expr_ast func_env env) e), env)

  and fold_stmt_list_inline func_env env stmts =
    let rec loop env acc = function
      | [] -> (List.rev acc, env)
      | s :: rest ->
          let s', env' = fold_stmt_inline func_env env s in
          let acc' = s' :: acc in
          if terminates s' then (List.rev acc', env') else loop env' acc' rest
    in
    loop env [] stmts
  in
  let rec loop env func_env acc = function
    | [] -> List.rev acc
    | TopDecl d :: rest ->
        let d', env' = fold_decl_with_inline func_env env d in
        loop env' func_env (TopDecl d' :: acc) rest
    | FuncDef f :: rest ->
        let params_shadow_consts =
          List.fold_left
            (fun env (p : Ast.ident) -> add_shadow env p.name)
            (push_scope env) f.params
        in
        let body, _ = fold_stmt_list_inline func_env params_shadow_consts f.body in
        let f = { f with body } in
        let func_env =
          match inline_def_of_func f with
          | Some def -> StringMap.add f.name.name def func_env
          | None -> func_env
        in
        loop env func_env (FuncDef f :: acc) rest
  in
  loop empty_env base_func_env [] program

let optimize_ast_impl program =
  let rec iterate fuel current =
    let next = optimize_ast_once current in
    if fuel = 0 || next = current then next else iterate (fuel - 1) next
  in
  iterate 2 program

(* Public AST optimizer entry point used by [Driver].  Keep this explicit in
   step20 so backend-only additions cannot accidentally hide or replace the
   driver-facing symbol. *)
let optimize_ast program = optimize_ast_impl program

let fold_unop op v =
  let v = i32 v in
  match op with
  | UPlus -> Some v
  | UMinus -> Some (i32 (Int64.neg v))
  | UNot -> Some (bool_int (not (truth v)))

let add_operand_temps acc = function
  | Tcg.Temp temp -> IntSet.add temp acc
  | Tcg.Imm _ -> acc

let local_places places =
  PlaceSet.filter
    (function
      | Tcg.Local _ -> true
      | Tcg.Global _ -> false)
    places

let place_is_global = function
  | Tcg.Global _ -> true
  | Tcg.Local _ -> false

let global_places places = PlaceSet.filter place_is_global places

let globals_in_func (f : Cfg.func) =
  List.fold_left
    (fun acc (block : Cfg.block) ->
      List.fold_left
        (fun acc instr ->
          match instr with
          | Tcg.Load (_, Tcg.Global label)
          | Tcg.Store (Tcg.Global label, _) ->
              PlaceSet.add (Tcg.Global label) acc
          | _ -> acc)
        acc block.body)
    PlaceSet.empty f.blocks

let locals_in_func (f : Cfg.func) =
  List.fold_left
    (fun acc (block : Cfg.block) ->
      List.fold_left
        (fun acc instr ->
          match instr with
          | Tcg.Load (_, (Tcg.Local _ as place))
          | Tcg.Store ((Tcg.Local _ as place), _) ->
              PlaceSet.add place acc
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> acc)
        acc block.body)
    PlaceSet.empty f.blocks

let stored_globals_in_func (f : Cfg.func) =
  List.fold_left
    (fun acc (block : Cfg.block) ->
      List.fold_left
        (fun acc instr ->
          match instr with
          | Tcg.Store (Tcg.Global label, _) -> PlaceSet.add (Tcg.Global label) acc
          | _ -> acc)
        acc block.body)
    PlaceSet.empty f.blocks

type func_effect_summary = {
  read_globals : PlaceSet.t;
  written_globals : PlaceSet.t;
}

let worst_case_effect_summary globals =
  { read_globals = globals; written_globals = globals }

let call_effect_summary summaries globals callee =
  match Hashtbl.find_opt summaries callee with
  | Some summary -> summary
  | None -> worst_case_effect_summary globals

let call_read_globals summaries globals callee =
  (call_effect_summary summaries globals callee).read_globals

let call_written_globals summaries globals callee =
  (call_effect_summary summaries globals callee).written_globals

let call_touched_globals summaries globals callee =
  PlaceSet.union
    (call_read_globals summaries globals callee)
    (call_written_globals summaries globals callee)

let equal_func_effect_summary a b =
  PlaceSet.equal a.read_globals b.read_globals
  && PlaceSet.equal a.written_globals b.written_globals

let summarize_func summaries globals (f : Cfg.func) =
  List.fold_left
    (fun summary (block : Cfg.block) ->
      List.fold_left
        (fun summary instr ->
          match instr with
          | Tcg.Load (_, (Tcg.Global _ as place)) ->
              { summary with read_globals = PlaceSet.add place summary.read_globals }
          | Tcg.Store ((Tcg.Global _ as place), _) ->
              { summary with written_globals = PlaceSet.add place summary.written_globals }
          | Tcg.Call (_, callee, _) ->
              let callee_summary = call_effect_summary summaries globals callee in
              {
                read_globals = PlaceSet.union summary.read_globals callee_summary.read_globals;
                written_globals =
                  PlaceSet.union summary.written_globals callee_summary.written_globals;
              }
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ -> summary)
        summary block.body)
    { read_globals = PlaceSet.empty; written_globals = PlaceSet.empty }
    f.blocks

let compute_func_summaries globals funcs =
  let summaries = Hashtbl.create (max 8 (List.length funcs)) in
  let empty_summary = { read_globals = PlaceSet.empty; written_globals = PlaceSet.empty } in
  List.iter (fun (f : Cfg.func) -> Hashtbl.replace summaries f.label empty_summary) funcs;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (f : Cfg.func) ->
        let summary = summarize_func summaries globals f in
        let prev =
          match Hashtbl.find_opt summaries f.label with
          | Some prev -> prev
          | None -> empty_summary
        in
        if not (equal_func_effect_summary summary prev) then (
          Hashtbl.replace summaries f.label summary;
          changed := true))
      funcs
  done;
  summaries

let operand_is_zero = function
  | Tcg.Imm 0L -> true
  | Tcg.Temp _ | Tcg.Imm _ -> false

let operand_is_one = function
  | Tcg.Imm 1L -> true
  | Tcg.Temp _ | Tcg.Imm _ -> false

let operand_is_minus_one = function
  | Tcg.Imm (-1L) -> true
  | Tcg.Temp _ | Tcg.Imm _ -> false

let operand_equal a b = a = b

let simplify_simple_instr = function
  | Tcg.Un (dst, op, src) -> (
      match src with
      | Tcg.Imm value -> (
          match fold_unop op value with
          | Some folded -> Tcg.Move (dst, Tcg.Imm folded)
          | None -> Tcg.Un (dst, op, src))
      | _ -> (
          match op with
          | UPlus -> Tcg.Move (dst, src)
          | _ -> Tcg.Un (dst, op, src)))
  | Tcg.Bin (dst, op, lhs, rhs) -> (
      match (lhs, rhs) with
      | Tcg.Imm a, Tcg.Imm b -> (
          match fold_binop op a b with
          | Some folded -> Tcg.Move (dst, Tcg.Imm folded)
          | None -> Tcg.Bin (dst, op, lhs, rhs))
      | _ -> (
          match op with
          | Add when operand_is_zero lhs -> Tcg.Move (dst, rhs)
          | Add when operand_is_zero rhs -> Tcg.Move (dst, lhs)
          | Sub when operand_is_zero rhs -> Tcg.Move (dst, lhs)
          | Sub when operand_equal lhs rhs -> Tcg.Move (dst, Tcg.Imm 0L)
          | Sub when operand_is_zero lhs -> Tcg.Un (dst, UMinus, rhs)
          | Mul when operand_is_zero lhs || operand_is_zero rhs -> Tcg.Move (dst, Tcg.Imm 0L)
          | Mul when operand_is_one lhs -> Tcg.Move (dst, rhs)
          | Mul when operand_is_one rhs -> Tcg.Move (dst, lhs)
          | Mul when operand_is_minus_one lhs -> Tcg.Un (dst, UMinus, rhs)
          | Mul when operand_is_minus_one rhs -> Tcg.Un (dst, UMinus, lhs)
          | Div when operand_is_one rhs -> Tcg.Move (dst, lhs)
          | Mod when operand_is_one rhs -> Tcg.Move (dst, Tcg.Imm 0L)
          | Eq when operand_equal lhs rhs -> Tcg.Move (dst, Tcg.Imm 1L)
          | Ne when operand_equal lhs rhs -> Tcg.Move (dst, Tcg.Imm 0L)
          | Lt when operand_equal lhs rhs -> Tcg.Move (dst, Tcg.Imm 0L)
          | Gt when operand_equal lhs rhs -> Tcg.Move (dst, Tcg.Imm 0L)
          | Le when operand_equal lhs rhs -> Tcg.Move (dst, Tcg.Imm 1L)
          | Ge when operand_equal lhs rhs -> Tcg.Move (dst, Tcg.Imm 1L)
          | _ -> Tcg.Bin (dst, op, lhs, rhs)))
  | instr -> instr

let is_compare_binop = function
  | Lt | Gt | Le | Ge | Eq | Ne -> true
  | Add | Sub | Mul | Div | Mod | LAnd | LOr -> false

let is_commutative_binop = function
  | Add | Mul | Eq | Ne -> true
  | Sub | Div | Mod | Lt | Gt | Le | Ge | LAnd | LOr -> false

type expr_key =
  | KeyUn of unop * Tcg.operand
  | KeyBin of binop * Tcg.operand * Tcg.operand
  | KeyLoad of Tcg.place

module ExprKeyOrd = struct
  type t = expr_key

  let compare = Stdlib.compare
end

module ExprKeyMap = Map.Make (ExprKeyOrd)

type avail_map = Tcg.operand ExprKeyMap.t

let empty_avail = ExprKeyMap.empty

type alias_map = Tcg.operand IntMap.t

let empty_alias = IntMap.empty

let normalize_bin_operands op lhs rhs =
  if not (is_commutative_binop op) then (lhs, rhs)
  else
    match (lhs, rhs) with
    | Tcg.Imm _, Tcg.Temp _ -> (rhs, lhs)
    | Tcg.Temp _, Tcg.Imm _ -> (lhs, rhs)
    | _ when Stdlib.compare lhs rhs > 0 -> (rhs, lhs)
    | _ -> (lhs, rhs)

let simplify_cfg_func (f : Cfg.func) =
  let simplify_instr instr =
    match simplify_simple_instr instr with
    | Tcg.Move (dst, Tcg.Temp src) when dst = src -> None
    | Tcg.Bin (dst, op, lhs, rhs) ->
        let lhs, rhs = normalize_bin_operands op lhs rhs in
        Some (Tcg.Bin (dst, op, lhs, rhs))
    | instr -> Some instr
  in
  let simplify_term = function
    | Cfg.BranchCompare (_, _, _, if_true, if_false) when if_true = if_false -> Cfg.Jump if_true
    | Cfg.BranchZero (_, if_zero, if_nonzero) when if_zero = if_nonzero -> Cfg.Jump if_zero
    | Cfg.BranchNonZero (_, if_nonzero, if_zero) when if_zero = if_nonzero -> Cfg.Jump if_zero
    | term -> term
  in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let body = List.filter_map simplify_instr block.body in
        let term = simplify_term block.term in
        { block with body; term; succs = Cfg.successors term })
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

let meet_avail a b =
  ExprKeyMap.merge
    (fun _ va vb ->
      match (va, vb) with
      | Some a, Some b when a = b -> Some a
      | _ -> None)
    a b

let kill_place_loads killed avail =
  ExprKeyMap.filter
    (fun key _ ->
      match key with
      | KeyLoad place -> not (PlaceSet.mem place killed)
      | KeyUn _ | KeyBin _ -> true)
    avail

let operand_has_temp temp = function
  | Tcg.Temp other -> other = temp
  | Tcg.Imm _ -> false

let expr_key_has_temp temp = function
  | KeyUn (_, src) -> operand_has_temp temp src
  | KeyBin (_, lhs, rhs) -> operand_has_temp temp lhs || operand_has_temp temp rhs
  | KeyLoad _ -> false

let avail_value_has_temp temp = function
  | Tcg.Temp other -> other = temp
  | Tcg.Imm _ -> false

let alias_value_has_temp temp = function
  | Tcg.Temp other -> other = temp
  | Tcg.Imm _ -> false

let equal_avail_map = ExprKeyMap.equal ( = )

let equal_alias_map = IntMap.equal ( = )

let meet_alias_map a b =
  IntMap.merge
    (fun _ va vb ->
      match (va, vb) with
      | Some a, Some b when a = b -> Some a
      | _ -> None)
    a b

let kill_temp_alias temp aliases =
  IntMap.filter
    (fun key value -> key <> temp && not (alias_value_has_temp temp value))
    aliases

let rec resolve_alias_operand aliases seen = function
  | Tcg.Imm _ as operand -> operand
  | Tcg.Temp temp ->
      if IntSet.mem temp seen then Tcg.Temp temp
      else
        match IntMap.find_opt temp aliases with
        | Some src -> resolve_alias_operand aliases (IntSet.add temp seen) src
        | None -> Tcg.Temp temp

let set_alias_fact aliases dst operand =
  if operand = Tcg.Temp dst then aliases else IntMap.add dst operand aliases

let retarget_alias_leader temp aliases =
  let members =
    IntMap.fold
      (fun alias value acc ->
        match value with
        | Tcg.Temp leader when leader = temp -> alias :: acc
        | Tcg.Temp _ | Tcg.Imm _ -> acc)
      aliases []
  in
  match members with
  | [] -> (aliases, None)
  | first :: rest ->
      let replacement = List.fold_left min first rest in
      let aliases =
        List.fold_left
          (fun aliases alias ->
            if alias = replacement then IntMap.remove alias aliases
            else IntMap.add alias (Tcg.Temp replacement) aliases)
          aliases members
      in
      (aliases, Some (Tcg.Temp replacement))

let kill_temp_gvn temp aliases avail =
  let aliases, replacement = retarget_alias_leader temp aliases in
  let avail = ExprKeyMap.filter (fun key _ -> not (expr_key_has_temp temp key)) avail in
  let avail =
    match replacement with
    | Some operand -> ExprKeyMap.map (fun value -> if value = Tcg.Temp temp then operand else value) avail
    | None -> ExprKeyMap.filter (fun _ value -> not (avail_value_has_temp temp value)) avail
  in
  (kill_temp_alias temp aliases, avail)

type gvn_state = {
  avail : avail_map;
  aliases : alias_map;
}

let empty_gvn_state = { avail = empty_avail; aliases = empty_alias }

let equal_gvn_state a b =
  equal_avail_map a.avail b.avail && equal_alias_map a.aliases b.aliases

let meet_gvn_state a b =
  { avail = meet_avail a.avail b.avail; aliases = meet_alias_map a.aliases b.aliases }

let transfer_gvn_instr summaries globals state instr =
  match instr with
  | Tcg.Move (dst, src) ->
      let src = resolve_alias_operand state.aliases IntSet.empty src in
      let instr = simplify_simple_instr (Tcg.Move (dst, src)) in
      let aliases, avail = kill_temp_gvn dst state.aliases state.avail in
      let aliases =
        match instr with
        | Tcg.Move (_, src) -> set_alias_fact aliases dst src
        | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> aliases
      in
      (instr, { avail; aliases })
  | Tcg.Un (dst, op, src) ->
      let src = resolve_alias_operand state.aliases IntSet.empty src in
      let instr = simplify_simple_instr (Tcg.Un (dst, op, src)) in
      let aliases, avail = kill_temp_gvn dst state.aliases state.avail in
      begin
        match instr with
        | Tcg.Move (_, src) -> (instr, { avail; aliases = set_alias_fact aliases dst src })
        | Tcg.Un (_, op, src) ->
            let key = KeyUn (op, src) in
            begin
              match ExprKeyMap.find_opt key avail with
              | Some value ->
                  ( Tcg.Move (dst, value),
                    { avail; aliases = set_alias_fact aliases dst value } )
              | None ->
                  (instr, { avail = ExprKeyMap.add key (Tcg.Temp dst) avail; aliases })
            end
        | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> (instr, { avail; aliases })
      end
  | Tcg.Bin (dst, op, lhs, rhs) ->
      let lhs = resolve_alias_operand state.aliases IntSet.empty lhs in
      let rhs = resolve_alias_operand state.aliases IntSet.empty rhs in
      let instr = simplify_simple_instr (Tcg.Bin (dst, op, lhs, rhs)) in
      let aliases, avail = kill_temp_gvn dst state.aliases state.avail in
      begin
        match instr with
        | Tcg.Move (_, src) -> (instr, { avail; aliases = set_alias_fact aliases dst src })
        | Tcg.Bin (_, op, lhs, rhs) ->
            let lhs, rhs = normalize_bin_operands op lhs rhs in
            let key = KeyBin (op, lhs, rhs) in
            begin
              match ExprKeyMap.find_opt key avail with
              | Some value ->
                  ( Tcg.Move (dst, value),
                    { avail; aliases = set_alias_fact aliases dst value } )
              | None ->
                  ( Tcg.Bin (dst, op, lhs, rhs),
                    { avail = ExprKeyMap.add key (Tcg.Temp dst) avail; aliases } )
            end
        | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> (instr, { avail; aliases })
      end
  | Tcg.Load (dst, place) ->
      let aliases, avail = kill_temp_gvn dst state.aliases state.avail in
      let key = KeyLoad place in
      begin
        match ExprKeyMap.find_opt key avail with
        | Some value ->
            (Tcg.Move (dst, value), { avail; aliases = set_alias_fact aliases dst value })
        | None ->
            (Tcg.Load (dst, place), { avail = ExprKeyMap.add key (Tcg.Temp dst) avail; aliases })
      end
  | Tcg.Store (place, value) ->
      let value = resolve_alias_operand state.aliases IntSet.empty value in
      let avail = ExprKeyMap.remove (KeyLoad place) state.avail in
      (Tcg.Store (place, value), { state with avail = ExprKeyMap.add (KeyLoad place) value avail })
  | Tcg.Call (dst, callee, args) ->
      let args = List.map (resolve_alias_operand state.aliases IntSet.empty) args in
      let aliases, avail =
        match dst with
        | Some temp -> kill_temp_gvn temp state.aliases state.avail
        | None -> (state.aliases, state.avail)
      in
      let avail = kill_place_loads (call_written_globals summaries globals callee) avail in
      (Tcg.Call (dst, callee, args), { avail; aliases })

type cp_fact =
  | CpUndef
  | CpConst of int64
  | CpNac

type cp_state = {
  temps : cp_fact IntMap.t;
  places : cp_fact PlaceMap.t;
}

let equal_cp_state a b =
  IntMap.equal ( = ) a.temps b.temps && PlaceMap.equal ( = ) a.places b.places

let equal_operand_map = IntMap.equal ( = )
let equal_place_operand_map = PlaceMap.equal ( = )

let empty_cp_state = { temps = IntMap.empty; places = PlaceMap.empty }

let fact_of_opt = function
  | Some fact -> fact
  | None -> CpUndef

let opt_of_fact = function
  | CpUndef -> None
  | fact -> Some fact

let meet_fact a b =
  match (a, b) with
  | CpUndef, x | x, CpUndef -> x
  | CpConst a, CpConst b when a = b -> CpConst a
  | CpConst _, CpConst _ -> CpNac
  | CpNac, _ | _, CpNac -> CpNac

let meet_int_map a b =
  IntMap.merge
    (fun _ va vb -> opt_of_fact (meet_fact (fact_of_opt va) (fact_of_opt vb)))
    a b

let meet_place_map a b =
  PlaceMap.merge
    (fun _ va vb -> opt_of_fact (meet_fact (fact_of_opt va) (fact_of_opt vb)))
    a b

let meet_cp_state a b =
  { temps = meet_int_map a.temps b.temps; places = meet_place_map a.places b.places }

let set_temp_fact state temp fact =
  {
    state with
    temps =
      (match fact with
      | CpUndef -> IntMap.remove temp state.temps
      | _ -> IntMap.add temp fact state.temps);
  }

let set_place_fact state place fact =
  {
    state with
    places =
      (match fact with
      | CpUndef -> PlaceMap.remove place state.places
      | _ -> PlaceMap.add place fact state.places);
  }

let get_temp_fact state temp = fact_of_opt (IntMap.find_opt temp state.temps)

let get_place_fact state place = fact_of_opt (PlaceMap.find_opt place state.places)

let eval_operand_fact state = function
  | Tcg.Imm value -> CpConst value
  | Tcg.Temp temp -> get_temp_fact state temp

let rewrite_operand_const state operand =
  match eval_operand_fact state operand with
  | CpConst value -> Tcg.Imm value
  | CpUndef | CpNac -> operand

let fold_fact_un op = function
  | CpConst value -> (
      match fold_unop op value with
      | Some folded -> CpConst folded
      | None -> CpNac)
  | CpUndef -> CpUndef
  | CpNac -> CpNac

let fold_fact_bin op a b =
  match (a, b) with
  | CpConst av, CpConst bv -> (
      match fold_binop op av bv with
      | Some folded -> CpConst folded
      | None -> CpNac)
  | CpNac, _ | _, CpNac -> CpNac
  | CpUndef, _ | _, CpUndef -> CpUndef

let kill_place_facts places state =
  PlaceSet.fold (fun place acc -> set_place_fact acc place CpNac) places state

let initial_cp_state global_init (f : Cfg.func) =
  let global_init =
    if f.name = "main" then global_init
    else PlaceMap.map (fun _ -> CpNac) global_init
  in
  let places =
    List.fold_left
      (fun places (param : Tcg.var) -> PlaceMap.add (Tcg.Local param.id) CpNac places)
      global_init f.params
  in
  { temps = IntMap.empty; places }

let fact_of_simple_instr state = function
  | Tcg.Move (_, src) -> eval_operand_fact state src
  | Tcg.Un (_, op, src) -> fold_fact_un op (eval_operand_fact state src)
  | Tcg.Bin (_, op, lhs, rhs) ->
      fold_fact_bin op (eval_operand_fact state lhs) (eval_operand_fact state rhs)
  | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> CpNac

let transfer_simple_instr summaries globals state instr =
  match instr with
  | Tcg.Move (dst, src) ->
      let src = rewrite_operand_const state src in
      let instr = simplify_simple_instr (Tcg.Move (dst, src)) in
      let fact = fact_of_simple_instr state instr in
      (instr, set_temp_fact state dst fact)
  | Tcg.Un (dst, op, src) ->
      let src = rewrite_operand_const state src in
      let instr = simplify_simple_instr (Tcg.Un (dst, op, src)) in
      let fact = fact_of_simple_instr state instr in
      (instr, set_temp_fact state dst fact)
  | Tcg.Bin (dst, op, lhs, rhs) ->
      let lhs = rewrite_operand_const state lhs in
      let rhs = rewrite_operand_const state rhs in
      let instr = simplify_simple_instr (Tcg.Bin (dst, op, lhs, rhs)) in
      let fact = fact_of_simple_instr state instr in
      (instr, set_temp_fact state dst fact)
  | Tcg.Load (dst, place) -> (
      let fact = get_place_fact state place in
      match fact with
      | CpConst value ->
          let instr = Tcg.Move (dst, Tcg.Imm value) in
          (instr, set_temp_fact state dst fact)
      | CpUndef | CpNac -> (Tcg.Load (dst, place), set_temp_fact state dst fact))
  | Tcg.Store (place, value) ->
      let value = rewrite_operand_const state value in
      let fact = eval_operand_fact state value in
      (Tcg.Store (place, value), set_place_fact state place fact)
  | Tcg.Call (dst, callee, args) ->
      let args = List.map (rewrite_operand_const state) args in
      let state = kill_place_facts (call_written_globals summaries globals callee) state in
      let state =
        match dst with
        | Some temp -> set_temp_fact state temp CpNac
        | None -> state
      in
      (Tcg.Call (dst, callee, args), state)

let transfer_terminator state (term : Cfg.terminator) =
  match term with
  | Cfg.Jump _ as term -> (term, state)
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      let cond = rewrite_operand_const state cond in
      let term =
        match eval_operand_fact state cond with
        | CpConst value -> Cfg.Jump (if value = 0L then if_zero else if_nonzero)
        | CpUndef | CpNac ->
            if if_zero = if_nonzero then Cfg.Jump if_zero
            else Cfg.BranchZero (cond, if_zero, if_nonzero)
      in
      (term, state)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      let cond = rewrite_operand_const state cond in
      let term =
        match eval_operand_fact state cond with
        | CpConst value -> Cfg.Jump (if value <> 0L then if_nonzero else if_zero)
        | CpUndef | CpNac ->
            if if_zero = if_nonzero then Cfg.Jump if_zero
            else Cfg.BranchNonZero (cond, if_nonzero, if_zero)
      in
      (term, state)
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      let lhs = rewrite_operand_const state lhs in
      let rhs = rewrite_operand_const state rhs in
      let term =
        match fold_fact_bin op (eval_operand_fact state lhs) (eval_operand_fact state rhs) with
        | CpConst value -> Cfg.Jump (if truth value then if_true else if_false)
        | CpUndef | CpNac ->
            if if_true = if_false then Cfg.Jump if_true
            else Cfg.BranchCompare (op, lhs, rhs, if_true, if_false)
      in
      (term, state)
  | Cfg.Return None -> (Cfg.Return None, state)
  | Cfg.Return (Some value) ->
      (Cfg.Return (Some (rewrite_operand_const state value)), state)

let run_transfer summaries globals state (block : Cfg.block) =
  let body_rev, state =
    List.fold_left
      (fun (acc, state) instr ->
        let instr, state = transfer_simple_instr summaries globals state instr in
        (instr :: acc, state))
      ([], state) block.body
  in
  let term, state = transfer_terminator state block.term in
  ({ block with body = List.rev body_rev; term; succs = Cfg.successors term }, state)

let executable_successors state (term : Cfg.terminator) =
  match term with
  | Cfg.Jump label -> [ label ]
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      if if_zero = if_nonzero then [ if_zero ]
      else
        begin
          match eval_operand_fact state cond with
          | CpConst value -> [ if value = 0L then if_zero else if_nonzero ]
          | CpNac -> [ if_zero; if_nonzero ]
          | CpUndef -> []
        end
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      if if_zero = if_nonzero then [ if_zero ]
      else
        begin
          match eval_operand_fact state cond with
          | CpConst value -> [ if value <> 0L then if_nonzero else if_zero ]
          | CpNac -> [ if_nonzero; if_zero ]
          | CpUndef -> []
        end
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      if if_true = if_false then [ if_true ]
      else
        begin
          match fold_fact_bin op (eval_operand_fact state lhs) (eval_operand_fact state rhs) with
          | CpConst value -> [ if truth value then if_true else if_false ]
          | CpNac -> [ if_true; if_false ]
          | CpUndef -> []
        end
  | Cfg.Return _ -> []

let compute_const_states global_init summaries globals (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block) f.blocks;
  let in_states = Hashtbl.create (List.length f.blocks) in
  let out_states = Hashtbl.create (List.length f.blocks) in
  let executable = ref (LabelSet.singleton f.entry) in
  let executable_edges = Hashtbl.create (max 8 (2 * List.length f.blocks)) in
  let entry_state = initial_cp_state global_init f in
  let meet_states = function
    | [] -> empty_cp_state
    | state :: rest -> List.fold_left meet_cp_state state rest
  in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (block : Cfg.block) ->
        if LabelSet.mem block.label !executable then (
          let pred_states =
            List.filter_map
              (fun pred ->
                if Hashtbl.mem executable_edges (pred, block.label) then
                  Hashtbl.find_opt out_states pred
                else None)
              block.preds
          in
          let in_state =
            if block.label = f.entry then meet_states (entry_state :: pred_states)
            else meet_states pred_states
          in
          let _, out_state = run_transfer summaries globals in_state block in
          let prev_in =
            match Hashtbl.find_opt in_states block.label with
            | Some state -> state
            | None -> empty_cp_state
          in
          let prev_out =
            match Hashtbl.find_opt out_states block.label with
            | Some state -> state
            | None -> empty_cp_state
          in
          if not (equal_cp_state in_state prev_in) then (
            Hashtbl.replace in_states block.label in_state;
            changed := true);
          if not (equal_cp_state out_state prev_out) then (
            Hashtbl.replace out_states block.label out_state;
            changed := true);
          List.iter
            (fun succ ->
              if Hashtbl.mem block_map succ
                 && not (Hashtbl.mem executable_edges (block.label, succ))
              then (
                Hashtbl.add executable_edges (block.label, succ) ();
                if not (LabelSet.mem succ !executable) then
                  executable := LabelSet.add succ !executable;
                changed := true))
            (executable_successors out_state block.term)))
      f.blocks
  done;
  (!executable, in_states)

let const_propagate_func global_init summaries globals (f : Cfg.func) =
  let executable, in_states = compute_const_states global_init summaries globals f in
  let blocks =
    List.filter_map
      (fun (block : Cfg.block) ->
        if LabelSet.mem block.label executable then
          let state =
            match Hashtbl.find_opt in_states block.label with
            | Some state -> state
            | None when block.label = f.entry -> initial_cp_state global_init f
            | None -> empty_cp_state
          in
          Some (fst (run_transfer summaries globals state block))
        else None)
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

let run_gvn_transfer summaries globals state (block : Cfg.block) =
  let body_rev, state =
    List.fold_left
      (fun (acc, state) instr ->
        let instr, state = transfer_gvn_instr summaries globals state instr in
        (instr :: acc, state))
      ([], state) block.body
  in
  let term =
    match block.term with
    | Cfg.Jump _ as term -> term
    | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
        let cond = resolve_alias_operand state.aliases IntSet.empty cond in
        begin
          match cond with
          | Tcg.Imm value -> Cfg.Jump (if value = 0L then if_zero else if_nonzero)
          | _ ->
              if if_zero = if_nonzero then Cfg.Jump if_zero
              else Cfg.BranchZero (cond, if_zero, if_nonzero)
        end
    | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
        let cond = resolve_alias_operand state.aliases IntSet.empty cond in
        begin
          match cond with
          | Tcg.Imm value -> Cfg.Jump (if value <> 0L then if_nonzero else if_zero)
          | _ ->
              if if_zero = if_nonzero then Cfg.Jump if_zero
              else Cfg.BranchNonZero (cond, if_nonzero, if_zero)
        end
    | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
        let lhs = resolve_alias_operand state.aliases IntSet.empty lhs in
        let rhs = resolve_alias_operand state.aliases IntSet.empty rhs in
        begin
          match (lhs, rhs) with
          | Tcg.Imm a, Tcg.Imm b -> (
              match fold_binop op a b with
              | Some value -> Cfg.Jump (if truth value then if_true else if_false)
              | None -> Cfg.BranchCompare (op, lhs, rhs, if_true, if_false))
          | _ ->
              if if_true = if_false then Cfg.Jump if_true
              else Cfg.BranchCompare (op, lhs, rhs, if_true, if_false)
        end
    | Cfg.Return None -> Cfg.Return None
    | Cfg.Return (Some value) ->
        Cfg.Return (Some (resolve_alias_operand state.aliases IntSet.empty value))
  in
  ({ block with body = List.rev body_rev; term; succs = Cfg.successors term }, state)

let compute_gvn_states summaries globals (f : Cfg.func) =
  let in_states = Hashtbl.create (List.length f.blocks) in
  let out_states = Hashtbl.create (List.length f.blocks) in
  let find_state table label =
    match Hashtbl.find_opt table label with
    | Some state -> state
    | None -> empty_gvn_state
  in
  let meet_preds preds =
    match preds with
    | [] -> empty_gvn_state
    | pred :: rest ->
        List.fold_left
          (fun acc pred -> meet_gvn_state acc (find_state out_states pred))
          (find_state out_states pred) rest
  in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (block : Cfg.block) ->
        let in_state = meet_preds block.preds in
        let _, out_state = run_gvn_transfer summaries globals in_state block in
        let prev_in = find_state in_states block.label in
        let prev_out = find_state out_states block.label in
        if not (equal_gvn_state in_state prev_in) then (
          Hashtbl.replace in_states block.label in_state;
          changed := true);
        if not (equal_gvn_state out_state prev_out) then (
          Hashtbl.replace out_states block.label out_state;
          changed := true))
      f.blocks
  done;
  in_states

let gvn_func summaries globals (f : Cfg.func) =
  let in_states = compute_gvn_states summaries globals f in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let state =
          match Hashtbl.find_opt in_states block.label with
          | Some state -> state
          | None -> empty_gvn_state
        in
        fst (run_gvn_transfer summaries globals state block))
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

let gvn_rewrite_instrs summaries globals instrs =
  let rewritten_rev, _ =
    List.fold_left
      (fun (acc, state) instr ->
        let instr, state = transfer_gvn_instr summaries globals state instr in
        (instr :: acc, state))
      ([], empty_gvn_state) instrs
  in
  List.rev rewritten_rev

let rec resolve_jump block_map seen label =
  if LabelSet.mem label seen then label
  else
    match Hashtbl.find_opt block_map label with
    | Some (block : Cfg.block) -> (
        match (block.body, block.term) with
        | [], Cfg.Jump next when next <> label ->
            resolve_jump block_map (LabelSet.add label seen) next
        | _ -> label)
    | _ -> label

let rewrite_term block_map = function
  | Cfg.Jump label -> Cfg.Jump (resolve_jump block_map LabelSet.empty label)
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      Cfg.BranchZero
        ( cond,
          resolve_jump block_map LabelSet.empty if_zero,
          resolve_jump block_map LabelSet.empty if_nonzero )
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      Cfg.BranchNonZero
        ( cond,
          resolve_jump block_map LabelSet.empty if_nonzero,
          resolve_jump block_map LabelSet.empty if_zero )
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      Cfg.BranchCompare
        ( op,
          lhs,
          rhs,
          resolve_jump block_map LabelSet.empty if_true,
          resolve_jump block_map LabelSet.empty if_false )
  | Cfg.Return value -> Cfg.Return value

let reachable_labels entry blocks =
  let block_map = Hashtbl.create (List.length blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block) blocks;
  let rec visit seen label =
    if LabelSet.mem label seen then seen
    else
      let seen = LabelSet.add label seen in
      match Hashtbl.find_opt block_map label with
      | None -> seen
      | Some block -> List.fold_left visit seen block.succs
  in
  visit LabelSet.empty entry

let thread_and_prune_func (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block) f.blocks;
  let threaded =
    List.map
      (fun (block : Cfg.block) ->
        let term = rewrite_term block_map block.term in
        { block with term; succs = Cfg.successors term })
      f.blocks
  in
  let threaded_func = Cfg.rebuild_edges { f with blocks = threaded } in
  let reachable = reachable_labels threaded_func.entry threaded_func.blocks in
  let blocks =
    List.filter (fun (block : Cfg.block) -> LabelSet.mem block.label reachable)
      threaded_func.blocks
  in
  Cfg.rebuild_edges { threaded_func with blocks }

let find_final_linear_merge_candidate (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block)
    f.blocks;
  let rec find = function
    | [] -> None
    | (block : Cfg.block) :: rest -> (
        match block.term with
        | Cfg.Jump succ when succ <> block.label && succ <> f.entry -> (
            match Hashtbl.find_opt block_map succ with
            | Some (succ_block : Cfg.block)
              when block.succs = [ succ ] && succ_block.preds = [ block.label ] ->
                Some (block.label, succ)
            | Some _ | None -> find rest)
        | Cfg.Jump _
        | Cfg.BranchZero _
        | Cfg.BranchNonZero _
        | Cfg.BranchCompare _
        | Cfg.Return _ ->
            find rest)
  in
  find f.blocks

let merge_final_linear_pair (f : Cfg.func) pred_label succ_label =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block)
    f.blocks;
  match
    ( Hashtbl.find_opt block_map pred_label,
      Hashtbl.find_opt block_map succ_label )
  with
  | Some (pred : Cfg.block), Some (succ : Cfg.block) ->
      let merged =
        {
          pred with
          body = pred.body @ succ.body;
          term = succ.term;
          succs = Cfg.successors succ.term;
        }
      in
      let blocks =
        List.filter_map
          (fun (block : Cfg.block) ->
            if block.label = succ_label then None
            else if block.label = pred_label then Some merged
            else Some block)
          f.blocks
      in
      Cfg.rebuild_edges { f with blocks }
  | _ -> f

let cfg_missing_targets (f : Cfg.func) =
  let labels =
    List.fold_left
      (fun acc (block : Cfg.block) -> LabelSet.add block.label acc)
      LabelSet.empty f.blocks
  in
  List.fold_left
    (fun missing (block : Cfg.block) ->
      List.fold_left
        (fun missing target ->
          if LabelSet.mem target labels then missing
          else LabelSet.add target missing)
        missing (Cfg.successors block.term))
    LabelSet.empty f.blocks

let cfg_targets_valid (f : Cfg.func) =
  LabelSet.is_empty (cfg_missing_targets f)

let debug_cfg_validation stage (f : Cfg.func) =
  if Sys.getenv_opt "TOYC_DEBUG_CFG_VALIDATE" <> None then
    let missing = cfg_missing_targets f |> LabelSet.elements in
    if missing <> [] then
      Printf.eprintf "cfg-invalid func=%s stage=%s missing=%s\n%!"
        f.name stage (String.concat "," missing)

let final_linear_merge_func (f : Cfg.func) =
  let before_blocks = List.length f.blocks in
  let rec loop merged current =
    match find_final_linear_merge_candidate current with
    | None -> (merged, current)
    | Some (pred, succ) ->
        let next = merge_final_linear_pair current pred succ in
        if not (cfg_targets_valid next) then begin
          debug_cfg_validation
            (Printf.sprintf "final-merge:%s->%s" pred succ) next;
          (merged, current)
        end else if List.length next.blocks >= List.length current.blocks then
          (merged, current)
        else loop (merged + 1) next
  in
  let merged, result = loop 0 f in
  if Sys.getenv_opt "TOYC_DEBUG_CFG_MERGE" <> None then
    Printf.eprintf
      "cfg-final-merge func=%s blocks=%d->%d merged=%d\n%!"
      f.name before_blocks (List.length result.blocks) merged;
  result

let live_out_t live_in_t (block : Cfg.block) =
  List.fold_left
    (fun acc succ ->
      let succ_live =
        match Hashtbl.find_opt live_in_t succ with
        | Some live -> live
        | None -> IntSet.empty
      in
      IntSet.union acc succ_live)
    IntSet.empty block.succs

let scan_simple_instr ?removable_calls summaries globals instr live_t live_p =
  match instr with
  | Tcg.Move (dst, src) ->
      if IntSet.mem dst live_t then
        ( Some instr,
          add_operand_temps (IntSet.remove dst live_t) src,
          live_p )
      else (None, live_t, live_p)
  | Tcg.Un (dst, _, src) ->
      if IntSet.mem dst live_t then
        ( Some instr,
          add_operand_temps (IntSet.remove dst live_t) src,
          live_p )
      else (None, live_t, live_p)
  | Tcg.Bin (dst, _, lhs, rhs) ->
      if IntSet.mem dst live_t then
        ( Some instr,
          add_operand_temps (add_operand_temps (IntSet.remove dst live_t) lhs) rhs,
          live_p )
      else (None, live_t, live_p)
  | Tcg.Load (dst, place) ->
      if IntSet.mem dst live_t then
        (Some instr, IntSet.remove dst live_t, PlaceSet.add place live_p)
      else (None, live_t, live_p)
  | Tcg.Store (place, value) ->
      if PlaceSet.mem place live_p then
        ( Some instr,
          add_operand_temps live_t value,
          PlaceSet.remove place live_p )
      else (None, live_t, live_p)
  | Tcg.Call (dst, callee, args) ->
      let result_dead =
        match dst with
        | None -> true
        | Some temp -> not (IntSet.mem temp live_t)
      in
      let removable =
        match removable_calls with
        | None -> false
        | Some table -> (
            match Hashtbl.find_opt table callee with
            | Some true -> true
            | Some false | None -> false)
      in
      if result_dead && removable then
        (* The call is proven side-effect-free and terminating, and its result
           is dead.  Removing it also means its argument computations need not
           be kept alive solely for this call. *)
        let live_t =
          match dst with
          | Some temp -> IntSet.remove temp live_t
          | None -> live_t
        in
        (None, live_t, live_p)
      else
        let kept_dst =
          match dst with
          | Some temp when IntSet.mem temp live_t -> Some temp
          | _ -> None
        in
        let live_t =
          List.fold_left add_operand_temps
            (match dst with
             | Some temp -> IntSet.remove temp live_t
             | None -> live_t)
            args
        in
        let written_globals = call_written_globals summaries globals callee in
        let read_globals = call_read_globals summaries globals callee in
        let live_p =
          PlaceSet.union
            (local_places live_p)
            (PlaceSet.union (PlaceSet.diff (global_places live_p) written_globals) read_globals)
        in
        (Some (Tcg.Call (kept_dst, callee, args)), live_t, live_p)

let scan_terminator ?return_globals globals (term : Cfg.terminator) live_t live_p =
  let return_globals =
    match return_globals with
    | Some return_globals -> return_globals
    | None -> globals
  in
  match term with
  | Cfg.Jump _ -> (term, live_t, live_p)
  | Cfg.BranchZero (cond, _, _) ->
      (term, add_operand_temps live_t cond, live_p)
  | Cfg.BranchNonZero (cond, _, _) ->
      (term, add_operand_temps live_t cond, live_p)
  | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
      (term, add_operand_temps (add_operand_temps live_t lhs) rhs, live_p)
  | Cfg.Return None -> (term, live_t, PlaceSet.union live_p return_globals)
  | Cfg.Return (Some value) ->
      ( term,
        add_operand_temps live_t value,
        PlaceSet.union live_p return_globals )

let scan_block ?return_globals ?removable_calls summaries globals (block : Cfg.block) live_t_out live_p_out =
  let term, live_t, live_p =
    scan_terminator ?return_globals globals block.term live_t_out live_p_out
  in
  let body_rev, live_t, live_p =
    List.fold_left
      (fun (acc, live_t, live_p) instr ->
        let kept, live_t, live_p = scan_simple_instr ?removable_calls summaries globals instr live_t live_p in
        let acc =
          match kept with
          | Some instr -> instr :: acc
          | None -> acc
        in
        (acc, live_t, live_p))
      ([], live_t, live_p) (List.rev block.body)
  in
  ({ block with body = body_rev; term }, live_t, live_p)

let table_find_or_empty table key empty =
  match Hashtbl.find_opt table key with
  | Some value -> value
  | None -> empty

type liveness_cache = {
  generation : int;
  entry_label : string;
  temp_count : int;
  blocks_key : Cfg.block list;
  live_in_t_cache : (string, IntSet.t) Hashtbl.t;
  live_in_p_cache : (string, PlaceSet.t) Hashtbl.t;
}

type dominator_cache = {
  generation : int;
  entry_label : string;
  temp_count : int;
  blocks_key : Cfg.block list;
  doms_cache : (string, LabelSet.t) Hashtbl.t;
}

let analysis_cache_generation = ref 0
let last_liveness_cache : liveness_cache option ref = ref None
let last_dominator_cache : dominator_cache option ref = ref None

let compute_liveness summaries globals (f : Cfg.func) =
  match !last_liveness_cache with
  | Some cache
    when !analysis_cache_generation <> 0
         && cache.generation = !analysis_cache_generation
         && cache.entry_label = f.entry
         && cache.temp_count = f.temp_count
         && cache.blocks_key = f.blocks ->
      (cache.live_in_t_cache, cache.live_in_p_cache)
  | Some _ | None ->
      let live_in_t = Hashtbl.create (List.length f.blocks) in
      let live_in_p = Hashtbl.create (List.length f.blocks) in
      let blocks = List.rev f.blocks in
      let changed = ref true in
      while !changed do
        changed := false;
        List.iter
          (fun (block : Cfg.block) ->
            let live_t_out =
              List.fold_left
                (fun acc succ ->
                  IntSet.union acc (table_find_or_empty live_in_t succ IntSet.empty))
                IntSet.empty block.succs
            in
            let live_p_out =
              List.fold_left
                (fun acc succ ->
                  PlaceSet.union acc (table_find_or_empty live_in_p succ PlaceSet.empty))
                PlaceSet.empty block.succs
            in
            let _, live_t_in, live_p_in = scan_block summaries globals block live_t_out live_p_out in
            if
              not (IntSet.equal live_t_in (table_find_or_empty live_in_t block.label IntSet.empty))
            then (
              Hashtbl.replace live_in_t block.label live_t_in;
              changed := true);
            if
              not
                (PlaceSet.equal live_p_in
                   (table_find_or_empty live_in_p block.label PlaceSet.empty))
            then (
              Hashtbl.replace live_in_p block.label live_p_in;
              changed := true))
          blocks
      done;
      if !analysis_cache_generation <> 0 then
        last_liveness_cache :=
          Some
            {
              generation = !analysis_cache_generation;
              entry_label = f.entry;
              temp_count = f.temp_count;
              blocks_key = f.blocks;
              live_in_t_cache = live_in_t;
              live_in_p_cache = live_in_p;
            };
      (live_in_t, live_in_p)

(* DCE sometimes knows that only a subset of globals must be observable when a
   function returns.  Keep the normal cached liveness above conservative for
   every other optimization, and use this uncached variant only for the
   context-sensitive dead-store analysis. *)
let compute_liveness_with_return_globals ?removable_calls summaries globals return_globals (f : Cfg.func) =
  let live_in_t = Hashtbl.create (List.length f.blocks) in
  let live_in_p = Hashtbl.create (List.length f.blocks) in
  let blocks = List.rev f.blocks in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (block : Cfg.block) ->
        let live_t_out =
          List.fold_left
            (fun acc succ ->
              IntSet.union acc (table_find_or_empty live_in_t succ IntSet.empty))
            IntSet.empty block.succs
        in
        let live_p_out =
          List.fold_left
            (fun acc succ ->
              PlaceSet.union acc (table_find_or_empty live_in_p succ PlaceSet.empty))
            PlaceSet.empty block.succs
        in
        let _, live_t_in, live_p_in =
          scan_block ~return_globals ?removable_calls summaries globals block live_t_out live_p_out
        in
        if
          not
            (IntSet.equal live_t_in
               (table_find_or_empty live_in_t block.label IntSet.empty))
        then (
          Hashtbl.replace live_in_t block.label live_t_in;
          changed := true);
        if
          not
            (PlaceSet.equal live_p_in
               (table_find_or_empty live_in_p block.label PlaceSet.empty))
        then (
          Hashtbl.replace live_in_p block.label live_p_in;
          changed := true))
      blocks
  done;
  (live_in_t, live_in_p)

let direct_callees_of_func (f : Cfg.func) =
  List.fold_left
    (fun acc (block : Cfg.block) ->
      List.fold_left
        (fun acc instr ->
          match instr with
          | Tcg.Call (_, callee, _) -> LabelSet.add callee acc
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ -> acc)
        acc block.body)
    LabelSet.empty f.blocks

let reachable_func_labels (funcs : Cfg.func list) =
  let by_label = Hashtbl.create (max 8 (List.length funcs)) in
  List.iter (fun (f : Cfg.func) -> Hashtbl.replace by_label f.label f) funcs;
  let rec find_main_label = function
    | [] -> None
    | (f : Cfg.func) :: rest ->
        if f.name = "main" then Some f.label else find_main_label rest
  in
  let main_label = find_main_label funcs in
  match main_label with
  | None -> LabelSet.empty
  | Some main_label ->
      let rec visit work seen =
        match work with
        | [] -> seen
        | label :: rest ->
            if LabelSet.mem label seen then visit rest seen
            else
              let seen = LabelSet.add label seen in
              let rest =
                match Hashtbl.find_opt by_label label with
                | None -> rest
                | Some f ->
                    LabelSet.fold
                      (fun callee acc ->
                        if Hashtbl.mem by_label callee then callee :: acc else acc)
                      (direct_callees_of_func f) rest
              in
              visit rest seen
      in
      visit [ main_label ] LabelSet.empty

let collect_call_global_demands summaries globals return_globals (f : Cfg.func) =
  let live_in_t, live_in_p =
    compute_liveness_with_return_globals summaries globals return_globals f
  in
  let demands = Hashtbl.create 8 in
  let add_demand callee needed =
    if not (PlaceSet.is_empty needed) then
      let prev =
        match Hashtbl.find_opt demands callee with
        | Some prev -> prev
        | None -> PlaceSet.empty
      in
      Hashtbl.replace demands callee (PlaceSet.union prev needed)
  in
  List.iter
    (fun (block : Cfg.block) ->
      let live_t_out =
        List.fold_left
          (fun acc succ ->
            IntSet.union acc (table_find_or_empty live_in_t succ IntSet.empty))
          IntSet.empty block.succs
      in
      let live_p_out =
        List.fold_left
          (fun acc succ ->
            PlaceSet.union acc (table_find_or_empty live_in_p succ PlaceSet.empty))
          PlaceSet.empty block.succs
      in
      let _, live_t, live_p =
        scan_terminator ~return_globals globals block.term live_t_out live_p_out
      in
      ignore
        (List.fold_left
           (fun (live_t, live_p) instr ->
             begin
               match instr with
               | Tcg.Call (_, callee, _) ->
                   let needed =
                     PlaceSet.inter
                       (global_places live_p)
                       (call_written_globals summaries globals callee)
                   in
                   add_demand callee needed
               | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ -> ()
             end;
             let _, live_t, live_p =
               scan_simple_instr summaries globals instr live_t live_p
             in
             (live_t, live_p))
           (live_t, live_p) (List.rev block.body)))
    f.blocks;
  demands

let compute_return_global_demands summaries globals (funcs : Cfg.func list) =
  let reachable = reachable_func_labels funcs in
  let demands = Hashtbl.create (max 8 (List.length funcs)) in
  List.iter
    (fun (f : Cfg.func) ->
      Hashtbl.replace demands f.label
        (if LabelSet.mem f.label reachable then PlaceSet.empty else globals))
    funcs;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (f : Cfg.func) ->
        if LabelSet.mem f.label reachable then
          let return_globals =
            match Hashtbl.find_opt demands f.label with
            | Some globals -> globals
            | None -> PlaceSet.empty
          in
          let call_demands =
            collect_call_global_demands summaries globals return_globals f
          in
          Hashtbl.iter
            (fun callee needed ->
              if LabelSet.mem callee reachable then
                let prev =
                  match Hashtbl.find_opt demands callee with
                  | Some prev -> prev
                  | None -> PlaceSet.empty
                in
                let next = PlaceSet.union prev needed in
                if not (PlaceSet.equal prev next) then (
                  Hashtbl.replace demands callee next;
                  changed := true))
            call_demands)
      funcs
  done;
  if Sys.getenv_opt "TOYC_DEBUG_GLOBAL_DSE" <> None then
    List.iter
      (fun (f : Cfg.func) ->
        let required =
          match Hashtbl.find_opt demands f.label with
          | Some required -> required
          | None -> globals
        in
        Printf.eprintf
          "global-dse-demand func=%s reachable=%b return_globals=%d/%d\n%!"
          f.name (LabelSet.mem f.label reachable)
          (PlaceSet.cardinal required) (PlaceSet.cardinal globals))
      funcs;
  demands

let collect_local_ids (f : Cfg.func) =
  List.fold_left
    (fun acc (var : Tcg.var) -> IntSet.add var.id acc)
    IntSet.empty (f.params @ f.locals)

let all_present values =
  let rec loop acc = function
    | [] -> Some (List.rev acc)
    | Some value :: rest -> loop (value :: acc) rest
    | None :: _ -> None
  in
  loop [] values

let all_same_operand = function
  | [] -> None
  | value :: rest ->
      if List.for_all (fun other -> other = value) rest then Some value else None

let get_or_create_phi_temp phi_temps fresh_temp key =
  match Hashtbl.find_opt phi_temps key with
  | Some temp -> temp
  | None ->
      let temp = fresh_temp () in
      Hashtbl.add phi_temps key temp;
      temp

let merge_incoming_operand preds lookup make_phi =
  match preds with
  | [] -> None
  | _ -> (
      match all_present (List.map lookup preds) with
      | Some values -> (
          match all_same_operand values with
          | Some value -> Some value
          | None -> Some (Tcg.Temp (make_phi ())))
      | None -> None)

(* mem2reg needs a slightly more optimistic merge at loop headers.
   During the first dataflow iterations a backedge may not have an out-value
   yet even though it will acquire one once the loop phi exists.  Treat a
   mixture of present and temporarily-missing predecessors as a provisional
   phi so the fixed point can bootstrap.  A later validation step still
   rejects the candidate if any predecessor remains genuinely undefined. *)
let merge_incoming_operand_mem2reg preds lookup make_phi =
  match preds with
  | [] -> None
  | _ ->
      let incoming = List.map lookup preds in
      begin
        match all_present incoming with
        | Some values -> (
            match all_same_operand values with
            | Some value -> Some value
            | None -> Some (Tcg.Temp (make_phi ())))
        | None ->
            if List.exists Option.is_some incoming then
              Some (Tcg.Temp (make_phi ()))
            else None
      end

let solve_forward_envs blocks ~empty_env ~equal_env ~compute_in_env ~transfer_env =
  let in_envs = Hashtbl.create (List.length blocks) in
  let out_envs = Hashtbl.create (List.length blocks) in
  let get_env table label = table_find_or_empty table label empty_env in
  let get_out label = get_env out_envs label in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (block : Cfg.block) ->
        let in_env = compute_in_env get_out block in
        let out_env = transfer_env in_env block in
        if not (equal_env in_env (get_env in_envs block.label)) then (
          Hashtbl.replace in_envs block.label in_env;
          changed := true);
        if not (equal_env out_env (get_env out_envs block.label)) then (
          Hashtbl.replace out_envs block.label out_env;
          changed := true))
      blocks
  done;
  (in_envs, out_envs, get_env)

let defs_temp = function
  | Tcg.Move (dst, _)
  | Tcg.Un (dst, _, _)
  | Tcg.Bin (dst, _, _, _)
  | Tcg.Load (dst, _) ->
      Some dst
  | Tcg.Store _ | Tcg.Call (None, _, _) -> None
  | Tcg.Call (Some dst, _, _) -> Some dst

let add_instr_use_temps live = function
  | Tcg.Move (_, src)
  | Tcg.Un (_, _, src) ->
      add_operand_temps live src
  | Tcg.Bin (_, _, lhs, rhs) ->
      add_operand_temps (add_operand_temps live lhs) rhs
  | Tcg.Load _ -> live
  | Tcg.Store (_, value) -> add_operand_temps live value
  | Tcg.Call (_, _, args) -> List.fold_left add_operand_temps live args

let add_term_use_temps live = function
  | Cfg.Jump _ | Cfg.Return None -> live
  | Cfg.BranchZero (cond, _, _)
  | Cfg.BranchNonZero (cond, _, _)
  | Cfg.Return (Some cond) ->
      add_operand_temps live cond
  | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
      add_operand_temps (add_operand_temps live lhs) rhs

let rewrite_operand_temp rename = function
  | Tcg.Imm _ as operand -> operand
  | Tcg.Temp temp -> Tcg.Temp (rename temp)

let rewrite_instr_temps rename = function
  | Tcg.Move (dst, src) ->
      Tcg.Move (rename dst, rewrite_operand_temp rename src)
  | Tcg.Un (dst, op, src) ->
      Tcg.Un (rename dst, op, rewrite_operand_temp rename src)
  | Tcg.Bin (dst, op, lhs, rhs) ->
      Tcg.Bin
        ( rename dst,
          op,
          rewrite_operand_temp rename lhs,
          rewrite_operand_temp rename rhs )
  | Tcg.Load (dst, place) -> Tcg.Load (rename dst, place)
  | Tcg.Store (place, value) -> Tcg.Store (place, rewrite_operand_temp rename value)
  | Tcg.Call (dst, callee, args) ->
      Tcg.Call
        ( Option.map rename dst,
          callee,
          List.map (rewrite_operand_temp rename) args )

let rewrite_term_temps rename = function
  | Cfg.Jump _ as term -> term
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      Cfg.BranchZero (rewrite_operand_temp rename cond, if_zero, if_nonzero)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      Cfg.BranchNonZero (rewrite_operand_temp rename cond, if_nonzero, if_zero)
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      Cfg.BranchCompare
        ( op,
          rewrite_operand_temp rename lhs,
          rewrite_operand_temp rename rhs,
          if_true,
          if_false )
  | Cfg.Return None -> Cfg.Return None
  | Cfg.Return (Some value) -> Cfg.Return (Some (rewrite_operand_temp rename value))

let copy_coalesce_func summaries globals (f : Cfg.func) =
  let debug_coalesce = Sys.getenv_opt "TOYC_DEBUG_COALESCE" <> None in
  if f.temp_count <= 1 then begin
    if debug_coalesce then
      Printf.eprintf
        "coalesce func=%s candidates=0 merged=0 removed_moves=0 temps=%d->%d\n%!"
        f.name f.temp_count f.temp_count;
    f
  end else
    let live_in_t, _ = compute_liveness summaries globals f in
    let interference = Array.make f.temp_count IntSet.empty in
    let add_edge a b =
      if a <> b && a >= 0 && b >= 0 && a < f.temp_count && b < f.temp_count then begin
        interference.(a) <- IntSet.add b interference.(a);
        interference.(b) <- IntSet.add a interference.(b)
      end
    in
    let candidates_rev = ref [] in
    List.iter
      (fun (block : Cfg.block) ->
        let live = ref (add_term_use_temps (live_out_t live_in_t block) block.term) in
        List.iter
          (fun instr ->
            begin
              match instr with
              | Tcg.Move (dst, Tcg.Temp src) when dst <> src ->
                  candidates_rev := (dst, src) :: !candidates_rev;
                  IntSet.iter
                    (fun temp -> if temp <> src then add_edge dst temp)
                    !live
              | _ -> (
                  match defs_temp instr with
                  | Some dst -> IntSet.iter (add_edge dst) !live
                  | None -> ())
            end;
            begin
              match defs_temp instr with
              | Some dst -> live := IntSet.remove dst !live
              | None -> ()
            end;
            live := add_instr_use_temps !live instr)
          (List.rev block.body))
      f.blocks;
    let parent = Array.init f.temp_count (fun temp -> temp) in
    let members = Array.init f.temp_count (fun temp -> IntSet.singleton temp) in
    let rec find temp =
      let p = parent.(temp) in
      if p = temp then temp
      else begin
        let root = find p in
        parent.(temp) <- root;
        root
      end
    in
    let components_interfere a b =
      let ra = find a in
      let rb = find b in
      if ra = rb then false
      else
        IntSet.fold
          (fun member found ->
            found
            || IntSet.fold
                 (fun neighbor found -> found || find neighbor = rb)
                 interference.(member) false)
          members.(ra) false
    in
    let merge a b =
      let ra = find a in
      let rb = find b in
      if ra = rb || components_interfere ra rb then false
      else begin
        let keep, drop = if ra <= rb then (ra, rb) else (rb, ra) in
        parent.(drop) <- keep;
        members.(keep) <- IntSet.union members.(keep) members.(drop);
        members.(drop) <- IntSet.empty;
        true
      end
    in
    let merged = ref 0 in
    List.iter
      (fun (dst, src) ->
        if dst >= 0 && src >= 0 && dst < f.temp_count && src < f.temp_count && merge dst src then
          incr merged)
      (List.rev !candidates_rev);
    if !merged = 0 then begin
      if debug_coalesce then
        Printf.eprintf
          "coalesce func=%s candidates=%d merged=0 removed_moves=0 temps=%d->%d\n%!"
          f.name (List.length !candidates_rev) f.temp_count f.temp_count;
      f
    end else
      let rename temp =
        if temp >= 0 && temp < f.temp_count then find temp else temp
      in
      let removed_moves = ref 0 in
      let rewrite_block (block : Cfg.block) =
        let body =
          List.filter_map
            (fun instr ->
              let instr = simplify_simple_instr (rewrite_instr_temps rename instr) in
              match instr with
              | Tcg.Move (dst, Tcg.Temp src) when dst = src ->
                  incr removed_moves;
                  None
              | _ -> Some instr)
            block.body
        in
        let term = rewrite_term_temps rename block.term in
        { block with body; term; succs = Cfg.successors term }
      in
      let blocks = List.map rewrite_block f.blocks in
      let rewritten = Cfg.rebuild_edges { f with blocks } in
      let used = ref IntSet.empty in
      let note_operand = function
        | Tcg.Temp temp -> used := IntSet.add temp !used
        | Tcg.Imm _ -> ()
      in
      let note_instr instr =
        begin
          match defs_temp instr with
          | Some temp -> used := IntSet.add temp !used
          | None -> ()
        end;
        match instr with
        | Tcg.Move (_, src)
        | Tcg.Un (_, _, src) -> note_operand src
        | Tcg.Bin (_, _, lhs, rhs) -> note_operand lhs; note_operand rhs
        | Tcg.Load _ -> ()
        | Tcg.Store (_, value) -> note_operand value
        | Tcg.Call (_, _, args) -> List.iter note_operand args
      in
      let note_term = function
        | Cfg.Jump _ | Cfg.Return None -> ()
        | Cfg.BranchZero (cond, _, _)
        | Cfg.BranchNonZero (cond, _, _)
        | Cfg.Return (Some cond) -> note_operand cond
        | Cfg.BranchCompare (_, lhs, rhs, _, _) -> note_operand lhs; note_operand rhs
      in
      List.iter
        (fun (block : Cfg.block) ->
          List.iter note_instr block.body;
          note_term block.term)
        rewritten.blocks;
      let dense = Hashtbl.create (IntSet.cardinal !used) in
      IntSet.elements !used
      |> List.iteri (fun next old -> Hashtbl.add dense old next);
      let dense_rename temp = Option.value ~default:temp (Hashtbl.find_opt dense temp) in
      let blocks =
        List.map
          (fun (block : Cfg.block) ->
            let body = List.map (rewrite_instr_temps dense_rename) block.body in
            let term = rewrite_term_temps dense_rename block.term in
            { block with body; term; succs = Cfg.successors term })
          rewritten.blocks
      in
      if debug_coalesce then
        Printf.eprintf
          "coalesce func=%s candidates=%d merged=%d removed_moves=%d temps=%d->%d\n%!"
          f.name (List.length !candidates_rev) !merged !removed_moves f.temp_count
          (IntSet.cardinal !used);
      Cfg.rebuild_edges
        { rewritten with temp_count = IntSet.cardinal !used; blocks }

let rewrite_term_target pred target redirects =
  match Hashtbl.find_opt redirects (pred, target) with
  | Some redirected -> redirected
  | None -> target

let redirect_successors pred redirects = function
  | Cfg.Jump label -> Cfg.Jump (rewrite_term_target pred label redirects)
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      Cfg.BranchZero
        ( cond,
          rewrite_term_target pred if_zero redirects,
          rewrite_term_target pred if_nonzero redirects )
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      Cfg.BranchNonZero
        ( cond,
          rewrite_term_target pred if_nonzero redirects,
          rewrite_term_target pred if_zero redirects )
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      Cfg.BranchCompare
        ( op,
          lhs,
          rhs,
          rewrite_term_target pred if_true redirects,
          rewrite_term_target pred if_false redirects )
  | Cfg.Return value -> Cfg.Return value

let build_parallel_copies fresh_temp copies =
  let rec remove_first target = function
    | [] -> []
    | copy :: rest ->
        if copy = target then rest else copy :: remove_first target rest
  in
  let rec schedule acc copies =
    let copies = List.filter (fun (dst, src) -> src <> Tcg.Temp dst) copies in
    match copies with
    | [] -> List.rev acc
    | _ ->
        let source_temps =
          List.fold_left
            (fun temps (_, src) ->
              match src with
              | Tcg.Temp temp -> IntSet.add temp temps
              | Tcg.Imm _ -> temps)
            IntSet.empty copies
        in
        begin
          match
            List.find_opt
              (fun (dst, _) -> not (IntSet.mem dst source_temps))
              copies
          with
          | Some ((dst, src) as copy) ->
              let instr = simplify_simple_instr (Tcg.Move (dst, src)) in
              schedule (instr :: acc) (remove_first copy copies)
          | None ->
              begin
                match copies with
                | (_, Tcg.Temp src_temp) :: _ ->
                    let snap_temp = fresh_temp () in
                    let snapshot =
                      simplify_simple_instr (Tcg.Move (snap_temp, Tcg.Temp src_temp))
                    in
                    let replacement = Tcg.Temp snap_temp in
                    let copies =
                      List.map
                        (fun (dst, src) ->
                          if src = Tcg.Temp src_temp then (dst, replacement)
                          else (dst, src))
                        copies
                    in
                    schedule (snapshot :: acc) copies
                | (_, Tcg.Imm _) :: _ ->
                    failwith "internal parallel-copy cycle"
                | [] -> List.rev acc
              end
        end
  in
  schedule [] copies

let place_edge_copies fresh_edge_label blocks edge_copies =
  let block_map = Hashtbl.create (List.length blocks) in
  List.iter
    (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block)
    blocks;
  let prepended_copies = Hashtbl.create 16 in
  let appended_copies = Hashtbl.create 16 in
  let redirects = Hashtbl.create 16 in
  let edge_blocks_rev = ref [] in
  let only_edge labels target =
    labels <> [] && List.for_all (fun label -> label = target) labels
  in
  List.iter
    (fun (pred, succ, body) ->
      match Hashtbl.find_opt block_map pred with
      | Some block when only_edge block.succs succ ->
          Hashtbl.replace appended_copies pred body
      | _ ->
          let succ_preds =
            match Hashtbl.find_opt block_map succ with
            | Some block -> block.preds
            | None -> []
          in
          if only_edge succ_preds pred then
            Hashtbl.replace prepended_copies succ body
          else
            let edge_label = fresh_edge_label () in
            Hashtbl.add redirects (pred, succ) edge_label;
            edge_blocks_rev :=
              {
                Cfg.label = edge_label;
                body;
                term = Cfg.Jump succ;
                preds = [];
                succs = [ succ ];
              }
              :: !edge_blocks_rev)
    edge_copies;
  List.map
    (fun (block : Cfg.block) ->
      let prefix =
        Option.value ~default:[] (Hashtbl.find_opt prepended_copies block.label)
      in
      let suffix =
        Option.value ~default:[] (Hashtbl.find_opt appended_copies block.label)
      in
      let term = redirect_successors block.label redirects block.term in
      {
        block with
        body = prefix @ block.body @ suffix;
        term;
        succs = Cfg.successors term;
      })
    blocks
  @ List.rev !edge_blocks_rev

let mem2reg_func ?(optimistic_loop_phi = false) (f : Cfg.func) =
  let all_candidates = collect_local_ids f in
  let rec attempt (current : Cfg.func) candidates =
    if IntSet.is_empty candidates then current
    else begin
      let next_temp = ref current.temp_count in
      let fresh_temp () =
        let temp = !next_temp in
        incr next_temp;
        temp
      in
      let seed_env =
        List.fold_left
          (fun env (param : Tcg.var) ->
            if IntSet.mem param.id candidates then
              let temp = fresh_temp () in
              IntMap.add param.id (Tcg.Temp temp) env
            else env)
          IntMap.empty current.params
      in
      let phi_temps = Hashtbl.create (max 8 (List.length current.blocks)) in
      let get_phi_temp label local_id =
        get_or_create_phi_temp phi_temps fresh_temp (label, local_id)
      in
      let compute_in_env get_out (block : Cfg.block) =
        if block.label = current.entry then seed_env
        else
          IntSet.fold
            (fun local_id env ->
              let merge =
                if optimistic_loop_phi then merge_incoming_operand_mem2reg
                else merge_incoming_operand
              in
              let keep_value =
                merge block.preds
                  (fun pred -> IntMap.find_opt local_id (get_out pred))
                  (fun () -> get_phi_temp block.label local_id)
              in
              match keep_value with
              | Some value -> IntMap.add local_id value env
              | None -> IntMap.remove local_id env)
            candidates IntMap.empty
      in
      let transfer_env env (block : Cfg.block) =
        List.fold_left
          (fun env instr ->
            match instr with
            | Tcg.Store (Tcg.Local id, value) when IntSet.mem id candidates -> IntMap.add id value env
            | _ -> env)
          env block.body
      in
      let in_envs, out_envs, get_env =
        solve_forward_envs current.blocks ~empty_env:IntMap.empty
          ~equal_env:equal_operand_map ~compute_in_env ~transfer_env
      in
      let failed = ref IntSet.empty in
      List.iter
        (fun (block : Cfg.block) ->
          let env = ref (get_env in_envs block.label) in
          List.iter
            (fun instr ->
              match instr with
              | Tcg.Load (_, Tcg.Local id) when IntSet.mem id candidates ->
                  if not (IntMap.mem id !env) then failed := IntSet.add id !failed
              | Tcg.Store (Tcg.Local id, value) when IntSet.mem id candidates ->
                  env := IntMap.add id value !env
              | _ -> ())
            block.body;
          Hashtbl.iter
            (fun (phi_label, local_id) _ ->
              if phi_label = block.label then
                match IntMap.find_opt local_id (get_env in_envs block.label) with
                | Some (Tcg.Temp _) ->
                    List.iter
                      (fun pred ->
                        if not (IntMap.mem local_id (get_env out_envs pred)) then
                          failed := IntSet.add local_id !failed)
                      block.preds
                | _ -> ())
            phi_temps)
        current.blocks;
      let succeeded = IntSet.diff candidates !failed in
      if Sys.getenv_opt "TOYC_DEBUG_MEM2REG_LOOP_PHI" <> None then
        Printf.eprintf
          "mem2reg-loop-phi func=%s mode=%s candidates=%d succeeded=%d failed=%d phis=%d\n%!"
          current.name
          (if optimistic_loop_phi then "optimistic" else "conservative")
          (IntSet.cardinal candidates)
          (IntSet.cardinal succeeded)
          (IntSet.cardinal !failed)
          (Hashtbl.length phi_temps);
      if IntSet.is_empty succeeded then current
      else
        let entry_seed_instrs =
          List.fold_left
            (fun acc (param : Tcg.var) ->
              if IntSet.mem param.id succeeded then
                match IntMap.find_opt param.id seed_env with
                | Some (Tcg.Temp temp) ->
                    simplify_simple_instr (Tcg.Load (temp, Tcg.Local param.id)) :: acc
                | Some (Tcg.Imm _) | None -> acc
              else acc)
            [] current.params
          |> List.rev
        in
        let rewrite_block (block : Cfg.block) =
          let rec rewrite env acc = function
            | [] -> List.rev acc
            | instr :: rest -> (
                match instr with
                | Tcg.Load (dst, Tcg.Local id) when IntSet.mem id succeeded -> (
                    match IntMap.find_opt id env with
                    | Some value ->
                        rewrite env (simplify_simple_instr (Tcg.Move (dst, value)) :: acc) rest
                    | None -> rewrite env (instr :: acc) rest)
                | Tcg.Store (Tcg.Local id, value) when IntSet.mem id succeeded ->
                    rewrite (IntMap.add id value env) acc rest
                | _ -> rewrite env (instr :: acc) rest)
          in
          let body =
            (if block.label = current.entry then entry_seed_instrs else [])
            @ rewrite (get_env in_envs block.label) [] block.body
          in
          { block with body }
        in
        let promoted_blocks = List.map rewrite_block current.blocks in
        let edge_id = ref 0 in
        let fresh_edge_label () =
          let id = !edge_id in
          incr edge_id;
          Printf.sprintf ".L%s_mem2reg_edge_%d" current.label id
        in
        let edge_copies_rev = ref [] in
        List.iter
          (fun (succ_block : Cfg.block) ->
            let phi_copies =
              IntSet.fold
                (fun local_id acc ->
                  match Hashtbl.find_opt phi_temps (succ_block.label, local_id) with
                  | Some phi_temp -> (
                      (* A provisional phi may have been created during an
                         intermediate solver iteration and later become
                         unnecessary.  Emit edge copies only when the final
                         fixed-point in-env actually uses this phi. *)
                      match IntMap.find_opt local_id (get_env in_envs succ_block.label) with
                      | Some (Tcg.Temp temp) when temp = phi_temp ->
                          (local_id, phi_temp) :: acc
                      | Some _ | None -> acc)
                  | None -> acc)
                succeeded []
            in
            if phi_copies <> [] then
              List.iter
                (fun pred ->
                  let pred_out = get_env out_envs pred in
                  let copies =
                    List.fold_left
                      (fun acc (local_id, phi_temp) ->
                        match IntMap.find_opt local_id pred_out with
                        | Some source when source <> Tcg.Temp phi_temp ->
                            (phi_temp, source) :: acc
                        | Some _ | None -> acc)
                      [] phi_copies
                  in
                  match build_parallel_copies fresh_temp (List.rev copies) with
                  | [] -> ()
                  | body ->
                      edge_copies_rev :=
                        (pred, succ_block.label, body) :: !edge_copies_rev)
                succ_block.preds)
          promoted_blocks;
        let blocks =
          place_edge_copies fresh_edge_label promoted_blocks (List.rev !edge_copies_rev)
        in
        let promoted = Cfg.rebuild_edges { current with temp_count = !next_temp; blocks } in
        if IntSet.is_empty !failed then promoted else attempt promoted !failed
    end
  in
  attempt f all_candidates

let promote_globals_func summaries globals (f : Cfg.func) =
  let stored_candidates = stored_globals_in_func f in
  let readonly_candidates = PlaceSet.diff (globals_in_func f) stored_candidates in
  let all_candidates = PlaceSet.union stored_candidates readonly_candidates in
  let rec attempt candidates =
    if PlaceSet.is_empty candidates then f
    else begin
      let writeback_candidates = PlaceSet.inter stored_candidates candidates in
      let preload_candidates = candidates in
      let next_temp = ref f.temp_count in
      let fresh_temp () =
        let temp = !next_temp in
        incr next_temp;
        temp
      in
      let phi_temps = Hashtbl.create (max 8 (List.length f.blocks)) in
      let entry_preloads_rev = ref [] in
      let entry_env =
        PlaceSet.fold
          (fun place env ->
            let temp = fresh_temp () in
            entry_preloads_rev :=
              simplify_simple_instr (Tcg.Load (temp, place)) :: !entry_preloads_rev;
            PlaceMap.add place (Tcg.Temp temp) env)
          preload_candidates PlaceMap.empty
      in
      let entry_preloads = List.rev !entry_preloads_rev in
      let kill_env_places places env =
        PlaceSet.fold (fun place env -> PlaceMap.remove place env) places env
      in
      let flush_env_places places env =
        PlaceSet.elements places
        |> List.filter_map (fun place ->
               match PlaceMap.find_opt place env with
               | Some value -> Some (Tcg.Store (place, value))
               | None -> None)
      in
      let get_phi_temp label place =
        get_or_create_phi_temp phi_temps fresh_temp (label, place)
      in
      let compute_in_env get_out (block : Cfg.block) =
        if block.label = f.entry then entry_env
        else
          PlaceSet.fold
            (fun place env ->
              let keep_value =
                merge_incoming_operand block.preds
                  (fun pred -> PlaceMap.find_opt place (get_out pred))
                  (fun () -> get_phi_temp block.label place)
              in
              match keep_value with
              | Some value -> PlaceMap.add place value env
              | None -> PlaceMap.remove place env)
            candidates PlaceMap.empty
      in
      let transfer_env env (block : Cfg.block) =
        List.fold_left
          (fun env instr ->
            match instr with
            | Tcg.Load (dst, place) when PlaceSet.mem place candidates ->
                PlaceMap.add place (Tcg.Temp dst) env
            | Tcg.Store (place, value) when PlaceSet.mem place candidates -> PlaceMap.add place value env
            | Tcg.Call (_, callee, _) ->
                kill_env_places
                  (PlaceSet.inter candidates (call_written_globals summaries globals callee))
                  env
            | _ -> env)
          env block.body
      in
      let in_envs, out_envs, get_env =
        solve_forward_envs f.blocks ~empty_env:PlaceMap.empty
          ~equal_env:equal_place_operand_map ~compute_in_env ~transfer_env
      in
      let failed = ref PlaceSet.empty in
      List.iter
        (fun (block : Cfg.block) ->
          if block.label <> f.entry then
            PlaceSet.iter
              (fun place ->
                if PlaceSet.mem place writeback_candidates then
                  let incoming =
                    List.map
                      (fun pred -> PlaceMap.find_opt place (get_env out_envs pred))
                      block.preds
                  in
                  match all_present incoming with
                  | Some _ -> ()
                  | None ->
                      if List.exists Option.is_some incoming then
                        failed := PlaceSet.add place !failed)
              candidates;
          let env = ref (get_env in_envs block.label) in
          List.iter
            (fun instr ->
              match instr with
                | Tcg.Load (dst, place) when PlaceSet.mem place candidates ->
                    env := PlaceMap.add place (Tcg.Temp dst) !env
                | Tcg.Store (place, value) when PlaceSet.mem place candidates ->
                    env := PlaceMap.add place value !env
                | Tcg.Call (_, callee, _) ->
                    env :=
                      kill_env_places
                        (PlaceSet.inter candidates (call_written_globals summaries globals callee))
                        !env
                | _ -> ())
            block.body;
          Hashtbl.iter
            (fun (phi_label, place) _ ->
              if phi_label = block.label then
                match PlaceMap.find_opt place (get_env in_envs block.label) with
                | Some (Tcg.Temp _) ->
                    List.iter
                      (fun pred ->
                        if not (PlaceMap.mem place (get_env out_envs pred)) then
                          failed := PlaceSet.add place !failed)
                      block.preds
                | _ -> ())
            phi_temps)
        f.blocks;
      if not (PlaceSet.is_empty !failed) then attempt (PlaceSet.diff candidates !failed)
      else
        let flush_env env =
          PlaceSet.elements writeback_candidates
          |> List.filter_map (fun place ->
                 match PlaceMap.find_opt place env with
                 | Some value -> Some (Tcg.Store (place, value))
                 | None -> None)
        in
        let rewrite_block (block : Cfg.block) =
          let rec rewrite env acc = function
            | [] -> (env, List.rev acc)
            | instr :: rest -> (
                match instr with
                | Tcg.Load (dst, place) when PlaceSet.mem place candidates -> (
                    match PlaceMap.find_opt place env with
                    | Some value ->
                        rewrite env (simplify_simple_instr (Tcg.Move (dst, value)) :: acc) rest
                    | None ->
                        rewrite (PlaceMap.add place (Tcg.Temp dst) env) (instr :: acc) rest)
                | Tcg.Store (place, value) when PlaceSet.mem place candidates ->
                    rewrite (PlaceMap.add place value env) acc rest
                | Tcg.Call (_, callee, _) as instr ->
                    let call_flushes =
                      PlaceSet.inter
                        writeback_candidates
                        (call_touched_globals summaries globals callee)
                    in
                    let call_kills =
                      PlaceSet.inter candidates (call_written_globals summaries globals callee)
                    in
                    let flushed = flush_env_places call_flushes env in
                    let acc = List.rev_append (flushed @ [ instr ]) acc in
                    rewrite (kill_env_places call_kills env) acc rest
                | _ -> rewrite env (instr :: acc) rest)
          in
          let env_out, body = rewrite (get_env in_envs block.label) [] block.body in
          let body =
            let body =
              if block.label = f.entry && entry_preloads <> [] then entry_preloads @ body else body
            in
            match block.term with
            | Cfg.Return _ -> body @ flush_env env_out
            | _ -> body
          in
          { block with body }
        in
        let promoted_blocks = List.map rewrite_block f.blocks in
        let edge_id = ref 0 in
        let fresh_edge_label () =
          let id = !edge_id in
          incr edge_id;
          Printf.sprintf ".L%s_gprom_edge_%d" f.label id
        in
        let edge_copies_rev = ref [] in
        List.iter
          (fun (succ_block : Cfg.block) ->
            let phi_copies =
              PlaceSet.fold
                (fun place acc ->
                  match Hashtbl.find_opt phi_temps (succ_block.label, place) with
                  | Some phi_temp -> (place, phi_temp) :: acc
                  | None -> acc)
                candidates []
            in
            if phi_copies <> [] then
              List.iter
                (fun pred ->
                  let pred_out = get_env out_envs pred in
                  let copies =
                    List.fold_left
                      (fun acc (place, phi_temp) ->
                        match PlaceMap.find_opt place pred_out with
                        | Some source when source <> Tcg.Temp phi_temp -> (phi_temp, source) :: acc
                        | Some _ | None -> acc)
                      [] phi_copies
                  in
                  match build_parallel_copies fresh_temp (List.rev copies) with
                  | [] -> ()
                  | body ->
                      edge_copies_rev :=
                        (pred, succ_block.label, body) :: !edge_copies_rev)
                succ_block.preds)
          promoted_blocks;
        let blocks =
          place_edge_copies fresh_edge_label promoted_blocks (List.rev !edge_copies_rev)
        in
        Cfg.rebuild_edges { f with temp_count = !next_temp; blocks }
    end
  in
  attempt all_candidates

let compute_dominators (f : Cfg.func) =
  match !last_dominator_cache with
  | Some cache
    when !analysis_cache_generation <> 0
         && cache.generation = !analysis_cache_generation
         && cache.entry_label = f.entry
         && cache.temp_count = f.temp_count
         && cache.blocks_key = f.blocks ->
      cache.doms_cache
  | Some _ | None ->
      let reachable = reachable_labels f.entry f.blocks in
      let reachable_blocks =
        List.filter (fun (block : Cfg.block) -> LabelSet.mem block.label reachable) f.blocks
      in
      let all_labels =
        List.fold_left
          (fun acc (block : Cfg.block) -> LabelSet.add block.label acc)
          LabelSet.empty reachable_blocks
      in
      let doms = Hashtbl.create (List.length reachable_blocks) in
      List.iter
        (fun (block : Cfg.block) ->
          Hashtbl.add doms block.label
            (if block.label = f.entry then LabelSet.singleton block.label else all_labels))
        reachable_blocks;
      let changed = ref true in
      while !changed do
        changed := false;
        List.iter
          (fun (block : Cfg.block) ->
            if block.label <> f.entry then
              let pred_doms =
                List.filter (fun pred -> LabelSet.mem pred reachable) block.preds
                |> List.map (fun pred -> table_find_or_empty doms pred all_labels)
              in
              let merged =
                match pred_doms with
                | [] -> all_labels
                | first :: rest -> List.fold_left LabelSet.inter first rest
              in
              let next_dom = LabelSet.add block.label merged in
              if
                not (LabelSet.equal next_dom (table_find_or_empty doms block.label LabelSet.empty))
              then (
                Hashtbl.replace doms block.label next_dom;
                changed := true))
          reachable_blocks
      done;
      if !analysis_cache_generation <> 0 then
        last_dominator_cache :=
          Some
            {
              generation = !analysis_cache_generation;
              entry_label = f.entry;
              temp_count = f.temp_count;
              blocks_key = f.blocks;
              doms_cache = doms;
            };
      doms

type licm_candidate =
  | LicmPure of Tcg.temp * Tcg.operand list
  | LicmLoad of Tcg.temp * Tcg.place

type loop_effects = {
  modified_places : PlaceSet.t;
  has_call : bool;
}

let licm_candidate_info = function
  | Tcg.Move (dst, src) -> Some (LicmPure (dst, [ src ]))
  | Tcg.Un (dst, _, src) -> Some (LicmPure (dst, [ src ]))
  | Tcg.Bin (dst, _, lhs, rhs) -> Some (LicmPure (dst, [ lhs; rhs ]))
  | Tcg.Load (dst, place) -> Some (LicmLoad (dst, place))
  | Tcg.Store _ | Tcg.Call _ -> None

let collect_loop_effects summaries globals loop blocks =
  List.fold_left
    (fun effects (block : Cfg.block) ->
      if not (LabelSet.mem block.label loop) then effects
      else
        List.fold_left
          (fun effects instr ->
            match instr with
            | Tcg.Store (place, _) ->
                { effects with modified_places = PlaceSet.add place effects.modified_places }
            | Tcg.Call (_, callee, _) ->
                {
                  modified_places =
                    PlaceSet.union effects.modified_places
                      (call_written_globals summaries globals callee);
                  has_call = true;
                }
            | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ -> effects)
          effects block.body)
    { modified_places = PlaceSet.empty; has_call = false }
    blocks

let rewrite_term_successor term ~from_label ~to_label =
  let rewrite label = if label = from_label then to_label else label in
  match term with
  | Cfg.Jump label -> Cfg.Jump (rewrite label)
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      Cfg.BranchZero (cond, rewrite if_zero, rewrite if_nonzero)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      Cfg.BranchNonZero (cond, rewrite if_nonzero, rewrite if_zero)
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      Cfg.BranchCompare (op, lhs, rhs, rewrite if_true, rewrite if_false)
  | Cfg.Return _ as term -> term

let loop_defined_temps loop get_block =
  LabelSet.fold
    (fun label acc ->
      let block : Cfg.block = get_block label in
      List.fold_left
        (fun acc instr ->
          match defs_temp instr with
          | Some temp -> IntSet.add temp acc
          | None -> acc)
        acc block.body)
    loop IntSet.empty

let get_block_exn block_map label =
  match Hashtbl.find_opt block_map label with
  | Some block -> block
  | None -> failwith ("internal missing block: " ^ label)

let natural_loop block_map header pred =
  let rec visit work seen =
    match work with
    | [] -> seen
    | label :: rest ->
        if LabelSet.mem label seen then visit rest seen
        else
          let seen = LabelSet.add label seen in
          match Hashtbl.find_opt block_map label with
          | Some (block : Cfg.block) -> visit (List.rev_append block.preds rest) seen
          | None -> visit rest seen
  in
  visit [ pred ] (LabelSet.singleton header)
let discover_natural_loops (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : Cfg.block) -> Hashtbl.add block_map block.label block)
    f.blocks;
  let doms = compute_dominators f in
  let backedges =
    List.fold_left
      (fun acc (block : Cfg.block) ->
        List.fold_left
          (fun acc succ ->
            if LabelSet.mem succ (table_find_or_empty doms block.label LabelSet.empty) then
              (block.label, succ) :: acc
            else acc)
          acc block.succs)
      [] f.blocks
  in
  let loops = Hashtbl.create 8 in
  List.iter
    (fun (pred, header) ->
      let loop = natural_loop block_map header pred in
      let merged = LabelSet.union loop (table_find_or_empty loops header LabelSet.empty) in
      Hashtbl.replace loops header merged)
    backedges;
  let headers =
    Hashtbl.fold (fun header loop acc -> (header, LabelSet.cardinal loop) :: acc) loops []
    |> List.sort (fun (_, a) (_, b) -> compare a b)
    |> List.map fst
  in
  (block_map, loops, headers)

let tailrec_elim_func (f : Cfg.func) =
  let tail_loop_label = f.entry in
  let next_temp = ref f.temp_count in
  let fresh_temp () =
    let temp = !next_temp in
    incr next_temp;
    temp
  in
  let tail_call_args_of_block (block : Cfg.block) =
    match block.term with
    | Cfg.Return (Some ret_operand) ->
        let rec peel current = function
          | [] -> None
          | instr :: rest -> (
              match (instr, current) with
              | Tcg.Move (dst, src), Tcg.Temp temp when dst = temp -> peel src rest
              | Tcg.Call (Some dst, callee, args), Tcg.Temp temp
                when dst = temp && callee = f.label ->
                  Some (List.rev rest, args)
              | _ -> None)
        in
        peel ret_operand (List.rev block.body)
    | Cfg.Return None | Cfg.Jump _ | Cfg.BranchZero _ | Cfg.BranchNonZero _ | Cfg.BranchCompare _ ->
        None
  in
  let build_parallel_param_stores args =
    if List.length args <> List.length f.params then None
    else
      let snapshots_rev = ref [] in
      let stores_rev = ref [] in
      List.iter2
        (fun (param : Tcg.var) arg ->
          let arg =
            match arg with
            | Tcg.Imm _ -> arg
            | Tcg.Temp temp ->
                let snap = fresh_temp () in
                snapshots_rev :=
                  simplify_simple_instr (Tcg.Move (snap, Tcg.Temp temp)) :: !snapshots_rev;
                Tcg.Temp snap
          in
          stores_rev := Tcg.Store (Tcg.Local param.id, arg) :: !stores_rev)
        f.params args;
      Some (List.rev !snapshots_rev @ List.rev !stores_rev)
  in
  let changed = ref false in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        match tail_call_args_of_block block with
        | None -> block
        | Some (prefix, args) -> (
            match build_parallel_param_stores args with
            | None -> block
            | Some stores ->
                changed := true;
                let term = Cfg.Jump tail_loop_label in
                { block with body = prefix @ stores; term; succs = Cfg.successors term }))
      f.blocks
  in
  if !changed then
    let existing_labels =
      List.fold_left
        (fun seen (block : Cfg.block) -> LabelSet.add block.label seen)
        LabelSet.empty blocks
    in
    let rec fresh_entry index =
      let label = Printf.sprintf ".L%s_tail_entry_%d" f.label index in
      if LabelSet.mem label existing_labels then fresh_entry (index + 1) else label
    in
    let new_entry = fresh_entry 0 in
    let entry_block =
      {
        Cfg.label = new_entry;
        body = [];
        term = Cfg.Jump tail_loop_label;
        preds = [];
        succs = [ tail_loop_label ];
      }
    in
    let blocks =
      List.fold_right
        (fun (block : Cfg.block) acc ->
          if block.label = tail_loop_label then entry_block :: block :: acc
          else block :: acc)
        blocks []
    in
    Cfg.rebuild_edges { f with entry = new_entry; temp_count = !next_temp; blocks }
  else f

let loop_canonicalize_func summaries globals (f : Cfg.func) =
  let next_preheader_id = ref 0 in
  let fresh_preheader_label () =
    let id = !next_preheader_id in
    incr next_preheader_id;
    Printf.sprintf ".L%s_canon_pre_%d" f.label id
  in
  let next_exit_id = ref 0 in
  let fresh_exit_label () =
    let id = !next_exit_id in
    incr next_exit_id;
    Printf.sprintf ".L%s_canon_exit_%d" f.label id
  in
  let next_prep_id = ref 0 in
  let fresh_prep_label () =
    let id = !next_prep_id in
    incr next_prep_id;
    Printf.sprintf ".L%s_canon_cmp_%d" f.label id
  in
  let rec apply (current : Cfg.func) =
    let live_in_t, live_in_p = compute_liveness summaries globals current in
    let _, loops, headers = discover_natural_loops current in
    if headers = [] then current
    else
      let current_blocks = Hashtbl.create (List.length current.blocks + (3 * List.length headers)) in
      List.iter
        (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block)
        current.blocks;
      let block_order = ref (List.map (fun (block : Cfg.block) -> block.label) current.blocks) in
      let current_entry = ref current.entry in
      let get_block = get_block_exn current_blocks in
      let update_block (block : Cfg.block) =
        Hashtbl.replace current_blocks block.label block
      in
      let insert_before label new_labels =
        block_order :=
          List.concat_map
            (fun current_label ->
              if current_label = label then List.rev_append new_labels [ current_label ]
              else [ current_label ])
            !block_order
      in
      let pure_prep_instr = function
        | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ -> true
        | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> false
      in
      let branch_targets = function
        | Cfg.BranchZero (_, if_zero, if_nonzero) -> Some (if_zero, if_nonzero)
        | Cfg.BranchNonZero (_, if_nonzero, if_zero) -> Some (if_nonzero, if_zero)
        | Cfg.BranchCompare (_, _, _, if_true, if_false) -> Some (if_true, if_false)
        | Cfg.Jump _ | Cfg.Return _ -> None
      in
      let branch_with_targets term if_true if_false =
        match term with
        | Cfg.BranchZero (cond, _, _) -> Cfg.BranchZero (cond, if_true, if_false)
        | Cfg.BranchNonZero (cond, _, _) -> Cfg.BranchNonZero (cond, if_true, if_false)
        | Cfg.BranchCompare (op, lhs, rhs, _, _) ->
            Cfg.BranchCompare (op, lhs, rhs, if_true, if_false)
        | Cfg.Jump _ | Cfg.Return _ -> term
      in
      let prune_jump_body (block : Cfg.block) next_label =
        let live_t =
          match Hashtbl.find_opt live_in_t next_label with
          | Some live -> live
          | None -> IntSet.empty
        in
        let live_p =
          match Hashtbl.find_opt live_in_p next_label with
          | Some live -> live
          | None -> PlaceSet.empty
        in
        let kept_rev, _, _ =
          List.fold_left
            (fun (acc, live_t, live_p) instr ->
              let kept, live_t, live_p = scan_simple_instr summaries globals instr live_t live_p in
              let acc =
                match kept with
                | Some instr -> instr :: acc
                | None -> acc
              in
              (acc, live_t, live_p))
            ([], live_t, live_p) (List.rev block.body)
        in
        List.rev kept_rev
      in
      let rec equivalent_linear_jump_chains seen_pairs a b =
        if a = b then Some a
        else if List.mem (a, b) seen_pairs || List.mem (b, a) seen_pairs then None
        else
          let a_block : Cfg.block = get_block a in
          let b_block : Cfg.block = get_block b in
          match (a_block.term, b_block.term) with
          | Cfg.Jump next_a, Cfg.Jump next_b ->
              let a_body = prune_jump_body a_block next_a in
              let b_body = prune_jump_body b_block next_b in
              if a_body <> b_body then None
              else if next_a = next_b then Some a
              else equivalent_linear_jump_chains ((a, b) :: seen_pairs) next_a next_b
          | _ -> None
      in
      let is_small_pure_control_body body =
        List.length body <= 4 && List.for_all pure_prep_instr body
      in
      let changed = ref false in
      List.iter
        (fun header ->
          let loop = table_find_or_empty loops header LabelSet.empty in
          let header_block : Cfg.block = get_block header in
          let outside_preds = List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds in
          let need_preheader =
            outside_preds <> []
            &&
            (List.length outside_preds > 1
            || List.exists
                 (fun pred ->
                   let pred_block : Cfg.block = get_block pred in
                   pred_block.succs <> [ header ])
                 outside_preds)
          in
          if need_preheader then begin
            changed := true;
            let preheader_label = fresh_preheader_label () in
            let redirects = Hashtbl.create (List.length outside_preds) in
            List.iter
              (fun pred -> Hashtbl.add redirects (pred, header) preheader_label)
              outside_preds;
            List.iter
              (fun pred ->
                let pred_block : Cfg.block = get_block pred in
                let term = redirect_successors pred redirects pred_block.term in
                update_block { pred_block with term; succs = Cfg.successors term })
              outside_preds;
            Hashtbl.add current_blocks preheader_label
              {
                Cfg.label = preheader_label;
                body = [];
                term = Cfg.Jump header;
                preds = [];
                succs = [ header ];
              };
            insert_before header [ preheader_label ];
            if header = !current_entry then current_entry := preheader_label
          end;
          let exit_labels =
            LabelSet.fold
              (fun label exits ->
                let block : Cfg.block = get_block label in
                List.fold_left
                  (fun exits succ -> if LabelSet.mem succ loop then exits else LabelSet.add succ exits)
                  exits block.succs)
              loop LabelSet.empty
          in
          LabelSet.iter
            (fun exit_label ->
              let exit_block : Cfg.block = get_block exit_label in
              let loop_preds = List.filter (fun pred -> LabelSet.mem pred loop) exit_block.preds in
              let outside_exit_preds =
                List.filter (fun pred -> not (LabelSet.mem pred loop)) exit_block.preds
              in
              if loop_preds <> [] && outside_exit_preds <> [] then begin
                changed := true;
                let dedicated_label = fresh_exit_label () in
                let redirects = Hashtbl.create (List.length loop_preds) in
                List.iter
                  (fun pred -> Hashtbl.add redirects (pred, exit_label) dedicated_label)
                  loop_preds;
                List.iter
                  (fun pred ->
                    let pred_block : Cfg.block = get_block pred in
                    let term = redirect_successors pred redirects pred_block.term in
                    update_block { pred_block with term; succs = Cfg.successors term })
                  loop_preds;
                Hashtbl.add current_blocks dedicated_label
                  {
                    Cfg.label = dedicated_label;
                    body = [];
                    term = Cfg.Jump exit_label;
                    preds = [];
                    succs = [ exit_label ];
                  };
                insert_before exit_label [ dedicated_label ]
              end)
            exit_labels;
          LabelSet.iter
            (fun label ->
              let block : Cfg.block = get_block label in
              let exits_loop =
                match branch_targets block.term with
                | Some (a, b) -> LabelSet.mem a loop <> LabelSet.mem b loop
                | None -> false
              in
              if
                label <> header
                && exits_loop
                && block.preds <> []
                && block.body <> []
                && is_small_pure_control_body block.body
              then begin
                changed := true;
                let prep_label = fresh_prep_label () in
                let redirects = Hashtbl.create (List.length block.preds) in
                List.iter
                  (fun pred -> Hashtbl.add redirects (pred, label) prep_label)
                  block.preds;
                List.iter
                  (fun pred ->
                    let pred_block : Cfg.block = get_block pred in
                    let term = redirect_successors pred redirects pred_block.term in
                    update_block { pred_block with term; succs = Cfg.successors term })
                  block.preds;
                Hashtbl.add current_blocks prep_label
                  {
                    Cfg.label = prep_label;
                    body = block.body;
                    term = Cfg.Jump label;
                    preds = [];
                    succs = [ label ];
                  };
               insert_before label [ prep_label ];
                update_block { block with body = [] };
                if label = !current_entry then current_entry := prep_label
              end)
            loop;
          LabelSet.iter
            (fun label ->
              let block : Cfg.block = get_block label in
              match branch_targets block.term with
              | Some (a, b)
                when LabelSet.mem a loop
                     && LabelSet.mem b loop
                     && a <> b -> (
                  match equivalent_linear_jump_chains [] a b with
                  | Some representative ->
                      changed := true;
                      let term = branch_with_targets block.term representative representative in
                      update_block { block with term; succs = Cfg.successors term }
                  | None -> ())
              | Some _ | None -> ())
            loop)
        headers;
      if !changed then
        let blocks = List.map get_block !block_order in
        let rebuilt = Cfg.rebuild_edges { current with entry = !current_entry; blocks } in
        let cleaned = thread_and_prune_func rebuilt in
        if cleaned = current then current else apply cleaned
      else current
  in
  apply f

let eliminate_dead_loops_func summaries globals (f : Cfg.func) =
  let debug_dead_loops = Sys.getenv_opt "TOYC_DEBUG_DEAD_LOOPS" <> None in
  let debugf fmt = Printf.ksprintf (fun s -> if debug_dead_loops then prerr_endline s) fmt in
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let live_in_t, live_in_p = compute_liveness summaries globals f in
    let current_blocks = Hashtbl.create (List.length f.blocks) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let current_entry = ref f.entry in
    let removed = ref LabelSet.empty in
    let changed = ref false in
    let current_block_list () = Hashtbl.fold (fun _ block acc -> block :: acc) current_blocks [] in
    let get_block = get_block_exn current_blocks in
    let block_exists label = Hashtbl.mem current_blocks label && not (LabelSet.mem label !removed) in
    List.iter
      (fun header ->
        if block_exists header then
          let loop = table_find_or_empty loops header LabelSet.empty in
          if not (LabelSet.exists (fun label -> LabelSet.mem label !removed) loop) then
            let header_block : Cfg.block = Hashtbl.find current_blocks header in
            let outside_preds =
              List.filter (fun pred -> not (LabelSet.mem pred loop) && block_exists pred) header_block.preds
            in
            let exit_labels =
              LabelSet.fold
                (fun label exits ->
                  match Hashtbl.find_opt current_blocks label with
                  | None -> exits
                  | Some (block : Cfg.block) ->
                      List.fold_left
                        (fun exits succ ->
                          if LabelSet.mem succ loop then exits else LabelSet.add succ exits)
                        exits block.succs)
                loop LabelSet.empty
            in
            match LabelSet.elements exit_labels with
            | [ exit_label ] when outside_preds <> [] || header = !current_entry ->
                let blocks_snapshot = current_block_list () in
                let effects = collect_loop_effects summaries globals loop blocks_snapshot in
                let modified_locals =
                  PlaceSet.filter (fun place -> not (place_is_global place)) effects.modified_places
                in
                let live_t_exit = table_find_or_empty live_in_t exit_label IntSet.empty in
                let live_p_exit = table_find_or_empty live_in_p exit_label PlaceSet.empty in
                let defined_temps = loop_defined_temps loop get_block in
                let has_global_store = PlaceSet.exists place_is_global effects.modified_places in
                if
                  not effects.has_call
                  && not has_global_store
                  && IntSet.is_empty (IntSet.inter defined_temps live_t_exit)
                  && PlaceSet.is_empty (PlaceSet.inter modified_locals live_p_exit)
                then begin
                  debugf "dead-loop-remove func=%s header=%s exit=%s entry=%s preds=%d loop_size=%d"
                    f.name header exit_label !current_entry (List.length outside_preds)
                    (LabelSet.cardinal loop);
                  changed := true;
                  List.iter
                    (fun pred ->
                      match Hashtbl.find_opt current_blocks pred with
                      | None -> ()
                      | Some (block : Cfg.block) ->
                          let term =
                            rewrite_term_successor block.term ~from_label:header ~to_label:exit_label
                          in
                          Hashtbl.replace current_blocks pred
                            { block with term; succs = Cfg.successors term })
                    outside_preds;
                  if header = !current_entry then current_entry := exit_label;
                  removed := LabelSet.union !removed loop
                end
            | _ -> ())
      headers;
    if !changed then
      let blocks =
        f.blocks
        |> List.filter (fun (block : Cfg.block) -> not (LabelSet.mem block.label !removed))
        |> List.map (fun (block : Cfg.block) ->
               match Hashtbl.find_opt current_blocks block.label with
               | Some block -> block
               | None -> block)
      in
      let threaded = Cfg.rebuild_edges { f with entry = !current_entry; blocks } in
      let reachable = reachable_labels threaded.entry threaded.blocks in
      let blocks =
        List.filter (fun (block : Cfg.block) -> LabelSet.mem block.label reachable) threaded.blocks
      in
      Cfg.rebuild_edges { threaded with blocks }
    else f

let load_place_invariant effects place =
  not (PlaceSet.mem place effects.modified_places)

type basic_induction_var = {
  phi_temp : Tcg.temp;
  outside_inputs : (Tcg.label * Tcg.operand) list;
  backedge_preds : Tcg.label list;
  step : int64;
}

type derived_expr_key =
  | DerivedScaled of int64
  | DerivedAdd of Tcg.operand * int64
  | DerivedSubBase of int64 * Tcg.operand
  | DerivedBaseMinus of Tcg.operand * int64

let temp_def_instrs_of_blocks temp_count blocks =
  let defs = Hashtbl.create (max 8 temp_count) in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (fun instr ->
          match defs_temp instr with
          | Some temp when not (Hashtbl.mem defs temp) -> Hashtbl.add defs temp instr
          | Some _ | None -> ())
        block.body)
    blocks;
  defs

let temp_def_instrs_map (f : Cfg.func) = temp_def_instrs_of_blocks f.temp_count f.blocks

let multi_def_temps_of_blocks temp_count blocks =
  let seen = Hashtbl.create (max 8 temp_count) in
  let multi_defs = ref IntSet.empty in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (fun instr ->
          match defs_temp instr with
          | Some temp ->
              if Hashtbl.mem seen temp then multi_defs := IntSet.add temp !multi_defs
              else Hashtbl.add seen temp ()
          | None -> ())
        block.body)
    blocks;
  !multi_defs

let analyze_temp_defs_of_blocks ?loop temp_count blocks =
  let loop_defs = ref IntSet.empty in
  let def_blocks = Hashtbl.create (max 8 temp_count) in
  let def_instrs = Hashtbl.create (max 8 temp_count) in
  let multi_defs = ref IntSet.empty in
  List.iter
    (fun (block : Cfg.block) ->
      let in_loop =
        match loop with
        | Some loop -> LabelSet.mem block.label loop
        | None -> false
      in
      List.iter
        (fun instr ->
          match defs_temp instr with
          | Some temp ->
              if in_loop then loop_defs := IntSet.add temp !loop_defs;
              Hashtbl.replace def_blocks temp block.label;
              if Hashtbl.mem def_instrs temp then
                multi_defs := IntSet.add temp !multi_defs
              else Hashtbl.add def_instrs temp instr
          | None -> ())
        block.body)
    blocks;
  (!loop_defs, def_blocks, def_instrs, !multi_defs)

let last_def_of_temp (block : Cfg.block) temp =
  let rec loop = function
    | [] -> None
    | instr :: rest -> (
        match defs_temp instr with
        | Some dst when dst = temp -> Some instr
        | Some _ | None -> loop rest)
  in
  loop (List.rev block.body)

let resolve_block_operand (block : Cfg.block) operand =
  let move_defs = Hashtbl.create (List.length block.body) in
  List.iter
    (function
      | Tcg.Move (dst, src) -> Hashtbl.replace move_defs dst src
      | _ -> ())
    block.body;
  let rec resolve seen = function
    | Tcg.Imm _ as operand -> operand
    | Tcg.Temp temp as operand ->
        if IntSet.mem temp seen then operand
        else
          match Hashtbl.find_opt move_defs temp with
          | Some src -> resolve (IntSet.add temp seen) src
          | None -> operand
  in
  resolve IntSet.empty operand

let trivial_phi_bridge_to succ_label (block : Cfg.block) =
  List.length block.preds = 1
  && block.succs = [ succ_label ]
  &&
  match block.term with
  | Cfg.Jump target when target = succ_label ->
      List.for_all
        (function
          | Tcg.Move _ -> true
          | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> false)
        block.body
  | Cfg.Jump _ | Cfg.BranchZero _ | Cfg.BranchNonZero _ | Cfg.BranchCompare _ | Cfg.Return _ ->
      false

let incoming_phi_chain get_block succ_label pred_label =
  let _ = succ_label in
  let rec walk seen label acc =
    if LabelSet.mem label seen then List.rev acc
    else
      let block : Cfg.block = get_block label in
      let acc = block :: acc in
      match block.preds with
      | [ prev ] ->
          let prev_block : Cfg.block = get_block prev in
          if trivial_phi_bridge_to label prev_block then
            walk (LabelSet.add label seen) prev acc
          else List.rev acc
      | _ -> List.rev acc
  in
  walk LabelSet.empty pred_label []

let incoming_update_chain get_block succ_label pred_label =
  let rec walk seen label acc =
    if LabelSet.mem label seen || label = succ_label then List.rev acc
    else
      let block : Cfg.block = get_block label in
      let acc = block :: acc in
      match block.preds with
      | [ prev ] -> walk (LabelSet.add label seen) prev acc
      | _ -> List.rev acc
  in
  walk LabelSet.empty pred_label []

let resolve_chain_operand chain operand =
  let move_defs = Hashtbl.create 8 in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (function
          | Tcg.Move (dst, src) when not (Hashtbl.mem move_defs dst) ->
              Hashtbl.add move_defs dst src
          | Tcg.Move _ -> ()
          | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> ())
        (List.rev block.body))
    chain;
  let rec resolve seen = function
    | Tcg.Imm _ as operand -> operand
    | Tcg.Temp temp as operand ->
        if IntSet.mem temp seen then operand
        else
          match Hashtbl.find_opt move_defs temp with
          | Some src -> resolve (IntSet.add temp seen) src
          | None -> operand
  in
  resolve IntSet.empty operand

let flatten_chain_block chain =
  let body =
    chain
    |> List.rev
    |> List.concat_map (fun (block : Cfg.block) -> block.body)
  in
  { Cfg.label = "<chain>"; body; term = Cfg.Return None; preds = []; succs = [] }

let move_dests_in_chain chain =
  List.fold_left
    (fun seen (block : Cfg.block) ->
      List.fold_left
        (fun seen instr ->
          match instr with
          | Tcg.Move (dst, _) -> IntSet.add dst seen
          | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> seen)
        seen block.body)
    IntSet.empty chain

let last_move_of_temp_on_chain chain temp =
  let rec block_loop = function
    | [] -> None
    | (block : Cfg.block) :: rest -> (
        let rec instr_loop = function
          | [] -> block_loop rest
          | instr :: instrs -> (
              match instr with
              | Tcg.Move (dst, src) when dst = temp -> Some src
              | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ ->
                  instr_loop instrs)
        in
        instr_loop (List.rev block.body))
  in
  block_loop chain

let last_def_of_temp_on_chain chain temp =
  let rec block_loop = function
    | [] -> None
    | (block : Cfg.block) :: rest -> (
        match last_def_of_temp block temp with
        | Some _ as found -> found
        | None -> block_loop rest)
  in
  block_loop chain

let last_def_of_temp_on_chain_with_block chain temp =
  let rec block_loop = function
    | [] -> None
    | (block : Cfg.block) :: rest -> (
        match last_def_of_temp block temp with
        | Some instr -> Some (block, instr, rest)
        | None -> block_loop rest)
  in
  block_loop chain

let rec chain_rest_from_label chain label =
  match chain with
  | [] -> None
  | (block : Cfg.block) :: rest ->
      if block.label = label then Some (block, rest) else chain_rest_from_label rest label

let def_instr_on_chain_or_global chain multi_defs def_instrs temp =
  if IntSet.mem temp multi_defs then last_def_of_temp_on_chain chain temp
  else Hashtbl.find_opt def_instrs temp

let def_instr_in_block_or_global (block : Cfg.block) multi_defs def_instrs temp =
  if IntSet.mem temp multi_defs then last_def_of_temp block temp
  else Hashtbl.find_opt def_instrs temp

let resolves_to_induction_temp_on_chain chain multi_defs def_instrs phi_temp operand =
  let rec loop seen = function
    | Tcg.Imm _ -> false
    | Tcg.Temp temp ->
        if temp = phi_temp then true
        else if IntSet.mem temp seen then false
        else
          match def_instr_on_chain_or_global chain multi_defs def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              loop (IntSet.add temp seen) src
          | Some _ | None -> false
  in
  loop IntSet.empty operand

let resolves_to_induction_temp_in_block block multi_defs def_instrs phi_temp operand =
  let rec loop seen = function
    | Tcg.Imm _ -> false
    | Tcg.Temp temp ->
        if temp = phi_temp then true
        else if IntSet.mem temp seen then false
        else
          match def_instr_in_block_or_global block multi_defs def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              loop (IntSet.add temp seen) src
          | Some _ | None -> false
  in
  loop IntSet.empty operand

let operand_static_int64_on_chain chain loop_defs multi_defs def_instrs operand =
  let rec loop seen = function
    | Tcg.Imm value -> Some value
    | Tcg.Temp temp ->
        if IntSet.mem temp seen || IntSet.mem temp loop_defs then None
        else
          match def_instr_on_chain_or_global chain multi_defs def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              loop (IntSet.add temp seen) src
          | Some (Tcg.Un (_, op, src)) ->
              Option.bind (loop (IntSet.add temp seen) src) (fold_unop op)
          | Some (Tcg.Bin (_, op, lhs, rhs)) -> (
              match (loop (IntSet.add temp seen) lhs, loop (IntSet.add temp seen) rhs) with
              | Some lhs, Some rhs -> fold_binop op lhs rhs
              | _ -> None)
          | Some (Tcg.Load _ | Tcg.Store _ | Tcg.Call _) | None -> None
  in
  loop IntSet.empty operand

let induction_step_of_instr_on_chain chain loop_defs multi_defs def_instrs phi_temp = function
  | Tcg.Bin (_, Add, lhs, rhs)
    when resolves_to_induction_temp_on_chain chain multi_defs def_instrs phi_temp lhs ->
      operand_static_int64_on_chain chain loop_defs multi_defs def_instrs rhs
  | Tcg.Bin (_, Add, lhs, rhs)
    when resolves_to_induction_temp_on_chain chain multi_defs def_instrs phi_temp rhs ->
      operand_static_int64_on_chain chain loop_defs multi_defs def_instrs lhs
  | Tcg.Bin (_, Sub, lhs, rhs)
    when resolves_to_induction_temp_on_chain chain multi_defs def_instrs phi_temp lhs ->
      Option.map Int64.neg
        (operand_static_int64_on_chain chain loop_defs multi_defs def_instrs rhs)
  | _ -> None

let pure_cfg_prep_instr = function
  | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ -> true
  | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> false

let resolves_to_temp multi_defs def_instrs target operand =
  let rec loop seen = function
    | Tcg.Imm _ -> false
    | Tcg.Temp temp ->
        if temp = target then true
        else if IntSet.mem temp seen || IntSet.mem temp multi_defs then false
        else
          match Hashtbl.find_opt def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              loop (IntSet.add temp seen) src
          | Some _ | None -> false
  in
  loop IntSet.empty operand

let resolves_to_induction_temp multi_defs def_instrs phi_temp operand =
  let rec loop seen = function
    | Tcg.Imm _ -> false
    | Tcg.Temp temp ->
        if temp = phi_temp then true
        else if IntSet.mem temp seen || IntSet.mem temp multi_defs then false
        else
          match Hashtbl.find_opt def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              loop (IntSet.add temp seen) src
          | Some _ | None -> false
  in
  loop IntSet.empty operand

let operand_static_int64 loop_defs multi_defs def_instrs operand =
  let rec loop seen = function
    | Tcg.Imm value -> Some value
    | Tcg.Temp temp ->
        if IntSet.mem temp seen || IntSet.mem temp multi_defs || IntSet.mem temp loop_defs then None
        else
          match Hashtbl.find_opt def_instrs temp with
          | Some (Tcg.Move (_, src)) -> loop (IntSet.add temp seen) src
          | Some (Tcg.Un (_, op, src)) -> Option.bind (loop (IntSet.add temp seen) src) (fold_unop op)
          | Some (Tcg.Bin (_, op, lhs, rhs)) -> (
              match (loop (IntSet.add temp seen) lhs, loop (IntSet.add temp seen) rhs) with
              | Some lhs, Some rhs -> fold_binop op lhs rhs
              | _ -> None)
          | Some (Tcg.Load _ | Tcg.Store _ | Tcg.Call _) | None -> None
  in
  loop IntSet.empty operand

let induction_step_of_instr loop_defs multi_defs def_instrs phi_temp = function
  | Tcg.Bin (_, Add, lhs, rhs) when resolves_to_induction_temp multi_defs def_instrs phi_temp lhs ->
      operand_static_int64 loop_defs multi_defs def_instrs rhs
  | Tcg.Bin (_, Add, lhs, rhs) when resolves_to_induction_temp multi_defs def_instrs phi_temp rhs ->
      operand_static_int64 loop_defs multi_defs def_instrs lhs
  | Tcg.Bin (_, Sub, lhs, rhs) when resolves_to_induction_temp multi_defs def_instrs phi_temp lhs ->
      Option.map Int64.neg (operand_static_int64 loop_defs multi_defs def_instrs rhs)
  | _ -> None

let mul_factor_of_instr multi_defs def_instrs phi_temp = function
  | Tcg.Bin (dst, Mul, lhs, Tcg.Imm factor)
    when resolves_to_induction_temp multi_defs def_instrs phi_temp lhs ->
      Some (dst, factor)
  | Tcg.Bin (dst, Mul, Tcg.Imm factor, rhs)
    when resolves_to_induction_temp multi_defs def_instrs phi_temp rhs ->
      Some (dst, factor)
  | _ -> None

let delta_instr dst base delta =
  if delta >= 0L then simplify_simple_instr (Tcg.Bin (dst, Add, Tcg.Temp base, Tcg.Imm delta))
  else simplify_simple_instr (Tcg.Bin (dst, Sub, Tcg.Temp base, Tcg.Imm Int64.(neg delta)))

let build_derived_backedge_update derived_phi delta =
  if delta = 0L then [] else [ delta_instr derived_phi derived_phi delta ]

let build_scaled_value dst source factor =
  match factor with
  | 0L -> [ Tcg.Move (dst, Tcg.Imm 0L) ]
  | 1L -> [ Tcg.Move (dst, source) ]
  | -1L -> [ simplify_simple_instr (Tcg.Bin (dst, Sub, Tcg.Imm 0L, source)) ]
  | _ -> [ simplify_simple_instr (Tcg.Bin (dst, Mul, source, Tcg.Imm factor)) ]

let build_derived_init key dst source =
  match key with
  | DerivedScaled factor -> build_scaled_value dst source factor
  | DerivedAdd (base, factor) ->
      build_scaled_value dst source factor
      @ [ simplify_simple_instr (Tcg.Bin (dst, Add, Tcg.Temp dst, base)) ]
  | DerivedSubBase (factor, base) ->
      build_scaled_value dst source factor
      @ [ simplify_simple_instr (Tcg.Bin (dst, Sub, Tcg.Temp dst, base)) ]
  | DerivedBaseMinus (base, factor) ->
      build_scaled_value dst source factor
      @ [ simplify_simple_instr (Tcg.Bin (dst, Sub, base, Tcg.Temp dst)) ]

let derived_key_temp_base = function
  | DerivedAdd (Tcg.Temp _, _)
  | DerivedSubBase (_, Tcg.Temp _)
  | DerivedBaseMinus (Tcg.Temp _, _) ->
      true
  | DerivedScaled _ | DerivedAdd _ | DerivedSubBase _ | DerivedBaseMinus _ -> false

let rec scaled_factor_of_operand multi_defs def_instrs phi_temp operand =
  match operand with
  | Tcg.Imm _ -> None
  | Tcg.Temp temp ->
      if temp = phi_temp then Some 1L
      else if IntSet.mem temp multi_defs then None
      else
        match Hashtbl.find_opt def_instrs temp with
        | Some (Tcg.Move (_, src))
        | Some (Tcg.Un (_, UPlus, src)) ->
            scaled_factor_of_operand multi_defs def_instrs phi_temp src
        | Some (Tcg.Un (_, UMinus, src))
          when resolves_to_induction_temp multi_defs def_instrs phi_temp src ->
            Some (-1L)
        | Some (Tcg.Bin (_, Sub, Tcg.Imm 0L, src))
          when resolves_to_induction_temp multi_defs def_instrs phi_temp src ->
            Some (-1L)
        | Some instr -> (
            match mul_factor_of_instr multi_defs def_instrs phi_temp instr with
            | Some (_, factor) -> Some factor
            | None -> None)
        | None -> None

let useful_derived_key = function
  | DerivedScaled factor -> factor <> 0L && factor <> 1L && factor <> -1L
  | DerivedAdd (_, factor)
  | DerivedSubBase (factor, _)
  | DerivedBaseMinus (_, factor) ->
      factor <> 0L

let worthwhile_derived_key key uses =
  if not (useful_derived_key key) then false
  else
    match key with
    | DerivedScaled factor -> factor <> 1L && factor <> -1L
    | DerivedAdd (_, factor)
    | DerivedSubBase (factor, _)
    | DerivedBaseMinus (_, factor) ->
        if factor <> 1L && factor <> -1L then true
        else List.length uses >= 2 || derived_key_temp_base key

let delta_of_derived_key step = function
  | DerivedScaled factor
  | DerivedAdd (_, factor)
  | DerivedSubBase (factor, _) ->
      Int64.mul step factor
  | DerivedBaseMinus (_, factor) -> Int64.neg (Int64.mul step factor)

let collect_loop_stable_phis header loop get_block def_blocks multi_defs def_instrs =
  let _ = def_blocks in
  let header_block : Cfg.block = get_block header in
  let pred_count = List.length header_block.preds in
  let pred_chains =
    List.map (fun pred -> (pred, incoming_phi_chain get_block header pred)) header_block.preds
  in
  let counts = Hashtbl.create (max 8 pred_count) in
  List.iter
    (fun (_, chain) ->
      IntSet.iter
        (fun dst ->
          let count = Option.value ~default:0 (Hashtbl.find_opt counts dst) in
          Hashtbl.replace counts dst (count + 1))
        (move_dests_in_chain chain))
    pred_chains;
  let phi_temps =
    Hashtbl.fold
      (fun temp count acc -> if count = pred_count then temp :: acc else acc)
      counts []
  in
  let backedge_preds = List.filter (fun pred -> LabelSet.mem pred loop) header_block.preds in
  List.fold_left
    (fun acc phi_temp ->
      let stable =
        backedge_preds <> []
        &&
        List.for_all
          (fun pred ->
            let chain =
              match List.assoc_opt pred pred_chains with
              | Some chain -> chain
              | None -> [ get_block pred ]
            in
            match last_move_of_temp_on_chain chain phi_temp with
            | Some src ->
                resolves_to_induction_temp
                  multi_defs def_instrs phi_temp (resolve_chain_operand chain src)
            | None -> false)
          backedge_preds
      in
      if stable then IntSet.add phi_temp acc else acc)
    IntSet.empty phi_temps

let collect_header_phi_temps header get_block =
  let header_block : Cfg.block = get_block header in
  let pred_count = List.length header_block.preds in
  let counts = Hashtbl.create (max 8 pred_count) in
  List.iter
    (fun pred ->
      IntSet.iter
        (fun dst ->
          let count = Option.value ~default:0 (Hashtbl.find_opt counts dst) in
          Hashtbl.replace counts dst (count + 1))
        (move_dests_in_chain (incoming_phi_chain get_block header pred)))
    header_block.preds;
  Hashtbl.fold
    (fun temp count acc -> if count = pred_count then IntSet.add temp acc else acc)
    counts IntSet.empty

let operand_loop_invariant
    loop_defs
    loop_stable_phis
    multi_defs
    def_instrs
    ready_temps
    operand
  =
  let rec resolve seen = function
    | Tcg.Imm _ -> true
    | Tcg.Temp temp ->
        if IntSet.mem temp ready_temps || IntSet.mem temp loop_stable_phis then true
        else if not (IntSet.mem temp loop_defs) then true
        else if IntSet.mem temp seen || IntSet.mem temp multi_defs then false
        else
          match Hashtbl.find_opt def_instrs temp with
          | Some (Tcg.Move (_, src)) -> resolve (IntSet.add temp seen) src
          | Some _ | None -> false
  in
  resolve IntSet.empty operand

let licm_invariant_candidate
    loop_defs
    loop_stable_phis
    multi_defs
    def_instrs
    ready_temps
    effects
    instr
  =
  match licm_candidate_info instr with
  | Some (LicmPure (dst, _)) when IntSet.mem dst multi_defs -> None
  | Some (LicmPure (dst, operands))
    when
      List.for_all
        (operand_loop_invariant
           loop_defs
           loop_stable_phis
           multi_defs
           def_instrs
           ready_temps)
        operands ->
      Some dst
  | Some (LicmLoad (dst, _)) when IntSet.mem dst multi_defs -> None
  | Some (LicmLoad (dst, place)) when load_place_invariant effects place -> Some dst
  | Some _ | None -> None

let derived_expr_of_instr loop_defs loop_stable_phis multi_defs def_instrs phi_temp = function
  | Tcg.Bin (dst, _, _, _) when dst = phi_temp -> None
  | Tcg.Bin (dst, Mul, lhs, Tcg.Imm factor)
    when resolves_to_induction_temp multi_defs def_instrs phi_temp lhs ->
      Some (dst, DerivedScaled factor)
  | Tcg.Bin (dst, Mul, Tcg.Imm factor, rhs)
    when resolves_to_induction_temp multi_defs def_instrs phi_temp rhs ->
      Some (dst, DerivedScaled factor)
  | Tcg.Bin (dst, Add, lhs, rhs) -> (
      match
        ( scaled_factor_of_operand multi_defs def_instrs phi_temp lhs,
          operand_loop_invariant
            loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty rhs,
          scaled_factor_of_operand multi_defs def_instrs phi_temp rhs,
          operand_loop_invariant
            loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty lhs )
      with
      | Some factor, true, _, _ -> Some (dst, DerivedAdd (rhs, factor))
      | _, _, Some factor, true -> Some (dst, DerivedAdd (lhs, factor))
      | _ -> None)
  | Tcg.Bin (dst, Sub, lhs, rhs) -> (
      match
        ( scaled_factor_of_operand multi_defs def_instrs phi_temp lhs,
          operand_loop_invariant
            loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty rhs,
          scaled_factor_of_operand multi_defs def_instrs phi_temp rhs,
          operand_loop_invariant
            loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty lhs )
      with
      | Some factor, true, _, _ -> Some (dst, DerivedSubBase (factor, rhs))
      | _, _, Some factor, true -> Some (dst, DerivedBaseMinus (lhs, factor))
      | _ -> None)
  | _ -> None

let collect_basic_induction_vars header loop get_block loop_defs multi_defs def_instrs =
  let header_block : Cfg.block = get_block header in
  let pred_count = List.length header_block.preds in
  let pred_chains =
    List.map (fun pred -> (pred, incoming_phi_chain get_block header pred)) header_block.preds
  in
  let chain_for_pred pred =
    match List.assoc_opt pred pred_chains with
    | Some chain -> chain
    | None -> [ get_block pred ]
  in
  let step_of_chain_source phi_temp chain src =
    let resolved = resolve_chain_operand chain src in
    match resolved with
    | Tcg.Imm _ -> None
    | Tcg.Temp temp -> (
        match def_instr_on_chain_or_global chain multi_defs def_instrs temp with
        | Some instr ->
            induction_step_of_instr_on_chain chain loop_defs multi_defs def_instrs phi_temp instr
        | None -> None)
  in
  let step_of_chain_def phi_temp chain =
    match last_def_of_temp_on_chain chain phi_temp with
    | Some (Tcg.Move (_, src)) -> step_of_chain_source phi_temp chain src
    | Some instr -> induction_step_of_instr_on_chain chain loop_defs multi_defs def_instrs phi_temp instr
    | None -> None
  in
  let counts = Hashtbl.create (max 8 pred_count) in
  List.iter
    (fun (_, chain) ->
      IntSet.iter
        (fun dst ->
          let count = Option.value ~default:0 (Hashtbl.find_opt counts dst) in
          Hashtbl.replace counts dst (count + 1))
        (move_dests_in_chain chain))
    pred_chains;
  let phi_temps =
    Hashtbl.fold
      (fun temp count acc -> if count = pred_count then temp :: acc else acc)
      counts []
  in
  let outside_preds =
    List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
  in
  let backedge_preds = List.filter (fun pred -> LabelSet.mem pred loop) header_block.preds in
  if outside_preds = [] || backedge_preds = [] then []
  else
    let phi_vars =
      List.filter_map
        (fun phi_temp ->
          let incoming =
            List.filter_map
              (fun (pred, chain) ->
                match last_move_of_temp_on_chain chain phi_temp with
                | Some src -> Some (pred, resolve_chain_operand chain src)
                | None -> None)
              pred_chains
          in
          if List.length incoming <> pred_count then None
          else
            let steps =
              List.filter_map
                (fun pred ->
                  match List.assoc_opt pred incoming with
                  | Some src -> step_of_chain_source phi_temp (chain_for_pred pred) src
                  | None -> None)
                backedge_preds
            in
            match steps with
            | [] -> None
            | step :: rest when List.length steps = List.length backedge_preds ->
                if List.for_all (Int64.equal step) rest then
                  Some
                    {
                      phi_temp;
                      outside_inputs =
                        List.filter (fun (pred, _) -> List.mem pred outside_preds) incoming;
                      backedge_preds;
                      step;
                    }
                else None
            | _ -> None)
        phi_temps
    in
    let seen_phi_temps =
      List.fold_left (fun acc iv -> IntSet.add iv.phi_temp acc) IntSet.empty phi_vars
    in
    let self_update_candidates =
      List.fold_left
        (fun acc pred ->
          List.fold_left
            (fun acc (block : Cfg.block) ->
              List.fold_left
                (fun acc instr ->
                  match defs_temp instr with
                  | Some dst when not (IntSet.mem dst seen_phi_temps) -> (
                      match
                        induction_step_of_instr_on_chain
                          (chain_for_pred pred)
                          loop_defs
                          multi_defs
                          def_instrs
                          dst
                          instr
                      with
                      | Some _ -> IntSet.add dst acc
                      | None -> acc)
                  | Some _ | None -> acc)
                acc block.body)
            acc (chain_for_pred pred))
        IntSet.empty backedge_preds
    in
    let self_vars =
      IntSet.fold
        (fun phi_temp acc ->
          let outside_inputs =
            List.filter_map
              (fun pred ->
                match last_def_of_temp_on_chain (chain_for_pred pred) phi_temp with
                | Some _ -> Some (pred, Tcg.Temp phi_temp)
                | None -> None)
              outside_preds
          in
          let steps =
            List.filter_map
              (fun pred ->
                step_of_chain_def phi_temp (chain_for_pred pred))
              backedge_preds
          in
          match steps with
          | [] -> acc
          | step :: rest when List.length steps = List.length backedge_preds ->
              if
                List.length outside_inputs = List.length outside_preds
                && List.for_all (Int64.equal step) rest
              then
                {
                  phi_temp;
                  outside_inputs;
                  backedge_preds;
                  step;
                }
                :: acc
              else acc
          | _ -> acc)
        self_update_candidates []
    in
    phi_vars @ self_vars

type counted_loop_kind =
  | CountUpLt of Tcg.operand * int64
  | CountUpLe of Tcg.operand * int64
  | CountDownGt of Tcg.operand * int64
  | CountDownGe of Tcg.operand * int64

type normalized_limit =
  | LimitConst of int64
  | LimitOperand of Tcg.operand * int64

type counted_loop_info = {
  control_iv : basic_induction_var;
  control_label : Tcg.label;
  inside_label : Tcg.label;
  exit_label : Tcg.label;
  kind : counted_loop_kind;
}

type summary_expr =
  | SummaryOperand of Tcg.operand
  | SummaryPlace of Tcg.place
  | SummaryUn of unop * summary_expr
  | SummaryBin of binop * summary_expr * summary_expr

type counted_reduction_step =
  | ReductionInvariant of summary_expr
  | ReductionAffine of {
      iv : basic_induction_var;
      coeff : summary_expr;
      bias : summary_expr;
    }
  | ReductionCarrierProgression of {
      carrier_temp : Tcg.temp;
      step_expr : summary_expr;
      carrier_subtract : bool;
      include_updated : bool;
    }

type counted_reduction_target =
  | ReductionTempTarget of Tcg.temp
  | ReductionPlaceTarget of Tcg.place

type counted_reduction = {
  target : counted_reduction_target;
  subtract : bool;
  step : counted_reduction_step;
  carrier_temp : Tcg.temp option;
  alias_temps : Tcg.temp list;
}

type counted_update =
  | CountedIv of basic_induction_var
  | CountedReduction of counted_reduction

let swap_compare = function
  | Lt -> Gt
  | Le -> Ge
  | Gt -> Lt
  | Ge -> Le
  | Eq -> Eq
  | Ne -> Ne
  | Add | Sub | Mul | Div | Mod | LAnd | LOr -> invalid_arg "swap_compare"

let invert_compare = function
  | Lt -> Ge
  | Le -> Gt
  | Gt -> Le
  | Ge -> Lt
  | Eq -> Ne
  | Ne -> Eq
  | Add | Sub | Mul | Div | Mod | LAnd | LOr -> invalid_arg "invert_compare"

let contains_substring text needle =
  let text_len = String.length text in
  let needle_len = String.length needle in
  let rec loop i =
    if i + needle_len > text_len then false
    else if String.sub text i needle_len = needle then true
    else loop (i + 1)
  in
  needle_len = 0 || loop 0

let is_unroll2_label label = contains_substring label "_unroll2_"
let is_unswitch_label label = contains_substring label "_unswitch_"
let is_rotate_guard_label label = contains_substring label "_rotate_guard_"

type loop_expr_range = {
  min_value : int64 option;
  max_value : int64 option;
}

let iv_bias_of_operand_in_block block multi_defs def_instrs phi_temp operand =
  let rec loop seen = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp as operand ->
        if
          resolves_to_induction_temp_in_block block multi_defs def_instrs phi_temp operand
          || resolves_to_induction_temp multi_defs def_instrs phi_temp operand
        then Some 0L
        else if IntSet.mem temp seen then None
        else
          match def_instr_in_block_or_global block multi_defs def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              loop (IntSet.add temp seen) src
          | Some (Tcg.Bin (_, Add, lhs, Tcg.Imm delta)) ->
              Option.map (fun bias -> Int64.add bias delta) (loop (IntSet.add temp seen) lhs)
          | Some (Tcg.Bin (_, Add, Tcg.Imm delta, rhs)) ->
              Option.map (fun bias -> Int64.add bias delta) (loop (IntSet.add temp seen) rhs)
          | Some (Tcg.Bin (_, Sub, lhs, Tcg.Imm delta)) ->
              Option.map (fun bias -> Int64.sub bias delta) (loop (IntSet.add temp seen) lhs)
          | Some _ | None -> None
  in
  loop IntSet.empty operand

let resolve_compare_operand_in_block block multi_defs def_instrs operand =
  let rec loop seen negate = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp ->
        if IntSet.mem temp seen then None
        else
          match def_instr_in_block_or_global block multi_defs def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              loop (IntSet.add temp seen) negate src
          | Some (Tcg.Un (_, UNot, src)) ->
              loop (IntSet.add temp seen) (not negate) src
          | Some (Tcg.Bin (_, op, lhs, rhs)) when is_compare_binop op ->
              Some ((if negate then invert_compare op else op), lhs, rhs)
          | Some _ | None -> None
  in
  loop IntSet.empty false operand

let range_of_counted_iv_expr kind expr_bias =
  match kind with
  | CountUpLt (Tcg.Imm bound, control_bias) ->
      {
        min_value = None;
        max_value = Some Int64.(sub (sub bound 1L) control_bias |> add expr_bias);
      }
  | CountUpLe (Tcg.Imm bound, control_bias) ->
      {
        min_value = None;
        max_value = Some Int64.(sub bound control_bias |> add expr_bias);
      }
  | CountDownGt (Tcg.Imm bound, control_bias) ->
      {
        min_value = Some Int64.(add (sub bound control_bias) expr_bias |> add 1L);
        max_value = None;
      }
  | CountDownGe (Tcg.Imm bound, control_bias) ->
      {
        min_value = Some Int64.(sub bound control_bias |> add expr_bias);
        max_value = None;
      }
  | CountUpLt _ | CountUpLe _ | CountDownGt _ | CountDownGe _ ->
      { min_value = None; max_value = None }

let compare_truth_from_range op range constant =
  match (range.min_value, range.max_value, op) with
  | _, Some max_value, Lt when max_value < constant -> Some true
  | Some min_value, _, Lt when min_value >= constant -> Some false
  | _, Some max_value, Le when max_value <= constant -> Some true
  | Some min_value, _, Le when min_value > constant -> Some false
  | Some min_value, _, Gt when min_value > constant -> Some true
  | _, Some max_value, Gt when max_value <= constant -> Some false
  | Some min_value, _, Ge when min_value >= constant -> Some true
  | _, Some max_value, Ge when max_value < constant -> Some false
  | Some min_value, Some max_value, Eq when min_value = constant && max_value = constant -> Some true
  | Some min_value, _, Eq when min_value > constant -> Some false
  | _, Some max_value, Eq when max_value < constant -> Some false
  | Some min_value, Some max_value, Ne when min_value = constant && max_value = constant -> Some false
  | Some min_value, _, Ne when min_value > constant -> Some true
  | _, Some max_value, Ne when max_value < constant -> Some true
  | _ -> None

let rewrite_term_labels rename = function
  | Cfg.Jump label -> Cfg.Jump (rename label)
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      Cfg.BranchZero (cond, rename if_zero, rename if_nonzero)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      Cfg.BranchNonZero (cond, rename if_nonzero, rename if_zero)
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      Cfg.BranchCompare (op, lhs, rhs, rename if_true, rename if_false)
  | Cfg.Return _ as term -> term

let rewrite_term rename_label rename_operand = function
  | Cfg.Jump label -> Cfg.Jump (rename_label label)
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      Cfg.BranchZero (rename_operand cond, rename_label if_zero, rename_label if_nonzero)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      Cfg.BranchNonZero (rename_operand cond, rename_label if_nonzero, rename_label if_zero)
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      Cfg.BranchCompare
        (op, rename_operand lhs, rename_operand rhs, rename_label if_true, rename_label if_false)
  | Cfg.Return None -> Cfg.Return None
  | Cfg.Return (Some value) -> Cfg.Return (Some (rename_operand value))

let branch_term_outcomes = function
  | Cfg.BranchZero (_, if_zero, if_nonzero) -> Some (if_zero, if_nonzero)
  | Cfg.BranchNonZero (_, if_nonzero, if_zero) -> Some (if_nonzero, if_zero)
  | Cfg.BranchCompare (_, _, _, if_true, if_false) -> Some (if_true, if_false)
  | Cfg.Jump _ | Cfg.Return _ -> None

let transparent_loop_connector (block : Cfg.block) =
  match block.term with
  | Cfg.Jump _ ->
      List.for_all
        (function
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ -> true
          | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> false)
        block.body
      && List.length block.body <= 4
  | Cfg.BranchZero _ | Cfg.BranchNonZero _ | Cfg.BranchCompare _ | Cfg.Return _ -> false

let branch_term_with_targets term if_true if_false =
  match term with
  | Cfg.BranchZero (cond, _, _) -> Cfg.BranchZero (cond, if_true, if_false)
  | Cfg.BranchNonZero (cond, _, _) -> Cfg.BranchNonZero (cond, if_true, if_false)
  | Cfg.BranchCompare (op, lhs, rhs, _, _) ->
      Cfg.BranchCompare (op, lhs, rhs, if_true, if_false)
  | Cfg.Jump _ | Cfg.Return _ -> term

let branch_compare_shape_in_block block multi_defs def_instrs = function
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) -> Some (op, lhs, rhs, if_true, if_false)
  | Cfg.BranchZero (cond, if_zero, if_nonzero) -> (
      match resolve_compare_operand_in_block block multi_defs def_instrs cond with
      | Some (op, lhs, rhs) -> Some (op, lhs, rhs, if_nonzero, if_zero)
      | None -> None)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) -> (
      match resolve_compare_operand_in_block block multi_defs def_instrs cond with
      | Some (op, lhs, rhs) -> Some (op, lhs, rhs, if_nonzero, if_zero)
      | None -> None)
  | Cfg.Jump _ | Cfg.Return _ -> None

let resolve_operand_before_loop loop_defs multi_defs def_instrs operand =
  let rec resolve seen = function
    | Tcg.Imm _ as operand -> Some operand
    | Tcg.Temp temp as operand ->
        if not (IntSet.mem temp loop_defs) then Some operand
        else if IntSet.mem temp seen || IntSet.mem temp multi_defs then None
        else
          match Hashtbl.find_opt def_instrs temp with
          | Some (Tcg.Move (_, src)) -> resolve (IntSet.add temp seen) src
          | Some _ | None -> None
  in
  resolve IntSet.empty operand

let operand_available_before_loop loop_defs multi_defs def_instrs operand =
  Option.is_some (resolve_operand_before_loop loop_defs multi_defs def_instrs operand)

let rewrite_branch_term_before_loop loop_defs multi_defs def_instrs = function
  | Cfg.BranchZero (cond, if_zero, if_nonzero) -> (
      match resolve_operand_before_loop loop_defs multi_defs def_instrs cond with
      | Some cond -> Some (Cfg.BranchZero (cond, if_zero, if_nonzero))
      | None -> None)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) -> (
      match resolve_operand_before_loop loop_defs multi_defs def_instrs cond with
      | Some cond -> Some (Cfg.BranchNonZero (cond, if_nonzero, if_zero))
      | None -> None)
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) -> (
      match
        ( resolve_operand_before_loop loop_defs multi_defs def_instrs lhs,
          resolve_operand_before_loop loop_defs multi_defs def_instrs rhs )
      with
      | Some lhs, Some rhs -> Some (Cfg.BranchCompare (op, lhs, rhs, if_true, if_false))
      | _ -> None)
  | Cfg.Jump _ | Cfg.Return _ -> None

let normalize_limit_operand loop_defs multi_defs def_instrs operand delta =
  match operand_static_int64 loop_defs multi_defs def_instrs operand with
  | Some constant -> Some (LimitConst Int64.(add constant delta))
  | None -> (
      match resolve_operand_before_loop loop_defs multi_defs def_instrs operand with
      | Some resolved -> Some (LimitOperand (resolved, delta))
      | None -> None)

let classify_counted_loop_header
    control_label
    loop
    loop_defs
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    get_block
    (block : Cfg.block)
  =
  let term = block.term in
  let invariant operand =
    operand_loop_invariant
      loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty operand
  in
  let match_known_iv operand =
    List.find_map
      (fun (iv : basic_induction_var) ->
        if
          resolves_to_induction_temp_in_block block multi_defs def_instrs iv.phi_temp operand
          || resolves_to_induction_temp multi_defs def_instrs iv.phi_temp operand
        then Some (iv, 0L)
        else None)
      ivs
  in
  let inloop_preds = List.filter (fun pred -> LabelSet.mem pred loop) block.preds in
  let snapshot_bias_in_block (iv : basic_induction_var) temp (pred_block : Cfg.block) =
    let rec scan trailing_step = function
      | [] -> None
      | instr :: rest ->
          let trailing_step =
            match defs_temp instr with
            | Some dst when dst = iv.phi_temp -> (
                match induction_step_of_instr loop_defs multi_defs def_instrs iv.phi_temp instr with
                | Some step -> Some step
                | None -> trailing_step)
            | Some _ | None -> trailing_step
          in
          match instr with
          | Tcg.Move (dst, src)
          | Tcg.Un (dst, UPlus, src)
            when dst = temp
                 && (resolves_to_induction_temp_in_block pred_block multi_defs def_instrs iv.phi_temp src
                    || resolves_to_induction_temp multi_defs def_instrs iv.phi_temp src) ->
              Some
                (match trailing_step with
                | Some step -> Int64.neg step
                | None -> 0L)
          | Tcg.Bin (dst, Add, lhs, Tcg.Imm delta)
            when dst = temp
                 && (resolves_to_induction_temp_in_block pred_block multi_defs def_instrs iv.phi_temp lhs
                    || resolves_to_induction_temp multi_defs def_instrs iv.phi_temp lhs) ->
              Some
                Int64.(
                  add delta
                    (match trailing_step with
                    | Some step -> neg step
                    | None -> 0L))
          | Tcg.Bin (dst, Add, Tcg.Imm delta, rhs)
            when dst = temp
                 && (resolves_to_induction_temp_in_block pred_block multi_defs def_instrs iv.phi_temp rhs
                    || resolves_to_induction_temp multi_defs def_instrs iv.phi_temp rhs) ->
              Some
                Int64.(
                  add delta
                    (match trailing_step with
                    | Some step -> neg step
                    | None -> 0L))
          | Tcg.Bin (dst, Sub, lhs, Tcg.Imm delta)
            when dst = temp
                 && (resolves_to_induction_temp_in_block pred_block multi_defs def_instrs iv.phi_temp lhs
                    || resolves_to_induction_temp multi_defs def_instrs iv.phi_temp lhs) ->
              Some
                Int64.(
                  sub
                    (match trailing_step with
                    | Some step -> neg step
                    | None -> 0L)
                    delta)
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ ->
              scan trailing_step rest
    in
    scan None (List.rev pred_block.body)
  in
  let match_snapshot_iv operand =
    match operand with
    | Tcg.Imm _ -> None
    | Tcg.Temp temp ->
        List.find_map
          (fun (iv : basic_induction_var) ->
            let biases =
              List.filter_map
                (fun pred ->
                  let chain = incoming_update_chain get_block control_label pred in
                  match chain with
                  | pred_block :: _ -> snapshot_bias_in_block iv temp pred_block
                  | [] -> None)
                inloop_preds
            in
            match biases with
            | [] -> None
            | bias :: rest
              when List.length biases = List.length inloop_preds
                   && List.for_all (Int64.equal bias) rest ->
                Some (iv, bias)
            | _ -> None)
          ivs
  in
  let rec control_iv_bias_of_operand seen = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp as operand -> (
        match match_known_iv operand with
        | Some match_ -> Some match_
        | None -> (
            match match_snapshot_iv operand with
            | Some match_ -> Some match_
            | None ->
            if IntSet.mem temp seen then None
            else
              match def_instr_in_block_or_global block multi_defs def_instrs temp with
              | Some (Tcg.Move (_, src))
              | Some (Tcg.Un (_, UPlus, src)) ->
                  control_iv_bias_of_operand (IntSet.add temp seen) src
              | Some (Tcg.Bin (_, Add, lhs, Tcg.Imm delta)) -> (
                  match control_iv_bias_of_operand (IntSet.add temp seen) lhs with
                  | Some (iv, bias) -> Some (iv, Int64.add bias delta)
                  | None -> control_iv_bias_of_operand (IntSet.add temp seen) lhs)
              | Some (Tcg.Bin (_, Add, Tcg.Imm delta, rhs)) -> (
                  match control_iv_bias_of_operand (IntSet.add temp seen) rhs with
                  | Some (iv, bias) -> Some (iv, Int64.add bias delta)
                  | None -> control_iv_bias_of_operand (IntSet.add temp seen) rhs)
               | Some (Tcg.Bin (_, Sub, lhs, Tcg.Imm delta)) -> (
                   match control_iv_bias_of_operand (IntSet.add temp seen) lhs with
                   | Some (iv, bias) -> Some (iv, Int64.sub bias delta)
                   | None -> control_iv_bias_of_operand (IntSet.add temp seen) lhs)
               | Some _ | None -> None))
  in
  let match_control_iv op lhs rhs =
    match (control_iv_bias_of_operand IntSet.empty lhs, invariant rhs) with
    | Some (iv, bias), true ->
        let step = iv.step in
        if step = 0L then None
        else
          (match (step, op) with
          | step, Lt when step > 0L -> Some (iv, CountUpLt (rhs, bias))
          | step, Le when step > 0L -> Some (iv, CountUpLe (rhs, bias))
          | step, Gt when step < 0L -> Some (iv, CountDownGt (rhs, bias))
          | step, Ge when step < 0L -> Some (iv, CountDownGe (rhs, bias))
          | _ -> None)
    | _ -> (
        match (control_iv_bias_of_operand IntSet.empty rhs, invariant lhs) with
        | Some (iv, bias), true ->
            let step = iv.step in
            if step = 0L then None
            else
              (match (step, op) with
              | step, Gt when step > 0L -> Some (iv, CountUpLt (lhs, bias))
              | step, Ge when step > 0L -> Some (iv, CountUpLe (lhs, bias))
              | step, Lt when step < 0L -> Some (iv, CountDownGt (lhs, bias))
              | step, Le when step < 0L -> Some (iv, CountDownGe (lhs, bias))
              | _ -> None)
        | _ -> None)
  in
  let classify_targets op lhs rhs if_true if_false =
    let true_in = LabelSet.mem if_true loop in
    let false_in = LabelSet.mem if_false loop in
    if true_in = false_in then None
    else if true_in then
      Option.map
        (fun (control_iv, kind) ->
          { control_iv; control_label; inside_label = if_true; exit_label = if_false; kind })
        (match_control_iv op lhs rhs)
    else
      Option.map
        (fun (control_iv, kind) ->
          { control_iv; control_label; inside_label = if_false; exit_label = if_true; kind })
        (match_control_iv (invert_compare op) lhs rhs)
  in
  let rec resolve_compare_operand seen negate = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp ->
        if IntSet.mem temp seen then None
        else
          match def_instr_in_block_or_global block multi_defs def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) ->
              resolve_compare_operand (IntSet.add temp seen) negate src
          | Some (Tcg.Un (_, UNot, src)) ->
              resolve_compare_operand (IntSet.add temp seen) (not negate) src
          | Some (Tcg.Bin (_, op, lhs, rhs)) when is_compare_binop op ->
              Some ((if negate then invert_compare op else op), lhs, rhs)
          | Some _ | None -> None
  in
  match term with
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      classify_targets op lhs rhs if_true if_false
  | Cfg.BranchZero (cond, if_zero, if_nonzero) -> (
      match resolve_compare_operand IntSet.empty false cond with
      | Some (op, lhs, rhs) -> classify_targets op lhs rhs if_nonzero if_zero
      | None -> None)
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) -> (
      match resolve_compare_operand IntSet.empty false cond with
      | Some (op, lhs, rhs) -> classify_targets op lhs rhs if_nonzero if_zero
      | None -> None)
  | Cfg.Jump _ | Cfg.Return _ -> None

let find_counted_loop_control
    loop
    loop_defs
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    get_block
  =
  LabelSet.elements loop
  |> List.find_map (fun label ->
         let block : Cfg.block = get_block label in
         match branch_term_outcomes block.term with
         | Some (a, b) when LabelSet.mem a loop <> LabelSet.mem b loop ->
              classify_counted_loop_header
                label
                loop
                loop_defs
                loop_stable_phis
                multi_defs
                def_instrs
                ivs
                get_block
                block
          | Some _ | None -> None)

let analyze_induction_vars header loop get_block loop_defs multi_defs def_instrs =
  collect_basic_induction_vars header loop get_block loop_defs multi_defs def_instrs

let analyze_counted_control header loop get_block loop_defs loop_stable_phis multi_defs def_instrs =
  let ivs = analyze_induction_vars header loop get_block loop_defs multi_defs def_instrs in
  ( ivs,
    find_counted_loop_control
      loop loop_defs loop_stable_phis multi_defs def_instrs ivs get_block )

let analyze_counted_loop header loop get_block temp_count blocks =
  let loop_defs, def_blocks, def_instrs, multi_defs =
    analyze_temp_defs_of_blocks ~loop temp_count blocks
  in
  let loop_stable_phis =
    collect_loop_stable_phis header loop get_block def_blocks multi_defs def_instrs
  in
  let ivs, control =
    analyze_counted_control header loop get_block loop_defs loop_stable_phis multi_defs def_instrs
  in
  (loop_defs, def_blocks, def_instrs, multi_defs, loop_stable_phis, ivs, control)

let linear_loop_path header loop get_block entry_label =
  let rec collapse_transparent_branch seen visiting label =
    if label = header || LabelSet.mem label seen then Some header
    else if LabelSet.mem label visiting || not (LabelSet.mem label loop) then None
    else
      let block : Cfg.block = get_block label in
      match block.term with
      | Cfg.Jump next when block.body = [] ->
          collapse_transparent_branch seen (LabelSet.add label visiting) next
      | _ -> None
  in
  let rec equivalent_linear_branch_path seen_pairs a b =
    if a = b then Some ([], LabelSet.empty, a)
    else if List.mem (a, b) seen_pairs || List.mem (b, a) seen_pairs then None
    else if not (LabelSet.mem a loop) || not (LabelSet.mem b loop) then None
    else
      let a_block : Cfg.block = get_block a in
      let b_block : Cfg.block = get_block b in
      if a_block.body <> b_block.body then None
      else
        match (a_block.term, b_block.term) with
        | Cfg.Jump next_a, Cfg.Jump next_b ->
            if next_a = next_b then
              Some ([ a_block ], LabelSet.of_list [ a; b ], next_a)
            else
              Option.map
                (fun (rep_path, seen_labels, next) ->
                  (a_block :: rep_path, LabelSet.add a (LabelSet.add b seen_labels), next))
                (equivalent_linear_branch_path ((a, b) :: seen_pairs) next_a next_b)
        | _ -> None
  in
  let rec walk seen acc label =
    if label = header then Some (List.rev acc, seen)
    else if not (LabelSet.mem label loop) || LabelSet.mem label seen then None
    else
      let block : Cfg.block = get_block label in
      match block.succs with
      | [ next ] -> walk (LabelSet.add label seen) (block :: acc) next
      | _ -> (
          match branch_term_outcomes block.term with
          | Some (a, b) -> (
              match equivalent_linear_branch_path [] a b with
              | Some (rep_path, branch_seen, next) ->
                  walk
                    (LabelSet.union (LabelSet.add label seen) branch_seen)
                    (List.rev_append rep_path acc)
                    next
              | None -> (
                  match block.body with
                  | [] -> (
                      match
                        ( collapse_transparent_branch seen (LabelSet.add label LabelSet.empty) a,
                          collapse_transparent_branch seen (LabelSet.add label LabelSet.empty) b )
                      with
                      | Some next_a, Some next_b when next_a = next_b ->
                          walk (LabelSet.add label seen) acc next_a
                      | _ -> None)
                  | _ -> None))
          | None -> None)
  in
  let rec transparent_connector_reaches seen visiting label =
    if label = header || LabelSet.mem label seen then true
    else if LabelSet.mem label visiting || not (LabelSet.mem label loop) then false
    else
      let block : Cfg.block = get_block label in
      match (block.body, block.term) with
      | [], Cfg.Jump next -> transparent_connector_reaches seen (LabelSet.add label visiting) next
      | _ -> false
  in
  match walk LabelSet.empty [] entry_label with
  | Some (path, seen) ->
      let leftovers = LabelSet.diff (LabelSet.remove header loop) seen in
      if
        LabelSet.is_empty leftovers
        || LabelSet.for_all (transparent_connector_reaches seen LabelSet.empty) leftovers
      then Some path
      else None
  | None -> None

let counted_loop_shape_supported header loop get_block entry_label =
  let rec collapse_empty_successor seen label =
    if label = header then Some header
    else if LabelSet.mem label seen || not (LabelSet.mem label loop) then None
    else
      let block : Cfg.block = get_block label in
      match (block.body, block.term) with
      | _, Cfg.Jump next when transparent_loop_connector block ->
          collapse_empty_successor (LabelSet.add label seen) next
      | [], _ -> (
          match branch_term_outcomes block.term with
          | Some (a, b) -> (
              match
                ( collapse_empty_successor (LabelSet.add label seen) a,
                  collapse_empty_successor (LabelSet.add label seen) b )
              with
              | Some next_a, Some next_b when next_a = next_b -> Some next_a
              | _ -> None)
          | None -> Some label)
      | _ -> Some label
  in
  let rec equivalent_linear_branches seen_pairs a b =
    if a = b then Some (LabelSet.empty, a)
    else if List.mem (a, b) seen_pairs || List.mem (b, a) seen_pairs then None
    else if not (LabelSet.mem a loop) || not (LabelSet.mem b loop) then None
    else
      let a_block : Cfg.block = get_block a in
      let b_block : Cfg.block = get_block b in
      if a_block.body <> b_block.body then None
      else
        match (a_block.term, b_block.term) with
        | Cfg.Jump next_a, Cfg.Jump next_b ->
            if next_a = next_b then
              Some (LabelSet.of_list [ a; b ], next_a)
            else
              Option.map
                (fun (seen_labels, next) ->
                  (LabelSet.add a (LabelSet.add b seen_labels), next))
                (equivalent_linear_branches ((a, b) :: seen_pairs) next_a next_b)
        | _ -> None
  in
  let rec walk seen label =
    if label = header then true
    else if LabelSet.mem label seen || not (LabelSet.mem label loop) then false
    else
      let seen = LabelSet.add label seen in
      let block : Cfg.block = get_block label in
      match block.succs with
      | [ next ] -> walk seen next
      | _ -> (
          match branch_term_outcomes block.term with
          | Some (a, b)
            when LabelSet.mem a loop && LabelSet.mem b loop -> (
              match equivalent_linear_branches [] a b with
              | Some (branch_seen, next) ->
                  let seen = LabelSet.union seen branch_seen in
                  walk seen next
              | None -> (
                  match
                    ( collapse_empty_successor seen a,
                      collapse_empty_successor seen b )
                  with
                  | Some next_a, Some next_b when next_a = next_b -> walk seen next_a
                  | _ -> false))
          | Some (a, b) when block.body = [] -> (
              match
                ( collapse_empty_successor seen a,
                  collapse_empty_successor seen b )
              with
              | Some next_a, Some next_b when next_a = next_b -> walk seen next_a
              | _ -> false)
          | Some _ | None -> false)
  in
  walk LabelSet.empty entry_label

let clamp_nonnegative_temp fresh_temp temp =
  let keep = fresh_temp () in
  let clamped = fresh_temp () in
  ( [ simplify_simple_instr (Tcg.Bin (keep, Ge, Tcg.Temp temp, Tcg.Imm 0L));
      simplify_simple_instr (Tcg.Bin (clamped, Mul, Tcg.Temp temp, Tcg.Temp keep)) ],
    clamped )

let build_floor_div fresh_temp numer_temp divisor =
  if divisor = 1L then ([], numer_temp)
  else
    let quotient = fresh_temp () in
    let remainder = fresh_temp () in
    let numer_neg = fresh_temp () in
    let rem_nz = fresh_temp () in
    let adjust = fresh_temp () in
    let floor = fresh_temp () in
    ( [ simplify_simple_instr
          (Tcg.Bin (quotient, Div, Tcg.Temp numer_temp, Tcg.Imm divisor));
        simplify_simple_instr
          (Tcg.Bin (remainder, Mod, Tcg.Temp numer_temp, Tcg.Imm divisor));
        simplify_simple_instr (Tcg.Bin (numer_neg, Lt, Tcg.Temp numer_temp, Tcg.Imm 0L));
        simplify_simple_instr (Tcg.Bin (rem_nz, Ne, Tcg.Temp remainder, Tcg.Imm 0L));
        simplify_simple_instr (Tcg.Bin (adjust, Mul, Tcg.Temp numer_neg, Tcg.Temp rem_nz));
        simplify_simple_instr (Tcg.Bin (floor, Sub, Tcg.Temp quotient, Tcg.Temp adjust)) ],
      floor )

let build_nonnegative_ceil_div fresh_temp numer_temp divisor =
  if divisor = 1L then clamp_nonnegative_temp fresh_temp numer_temp
  else
    let quotient = fresh_temp () in
    let remainder = fresh_temp () in
    let numer_pos = fresh_temp () in
    let rem_nz = fresh_temp () in
    let extra = fresh_temp () in
    let raw = fresh_temp () in
    let clamp_instrs, trip = clamp_nonnegative_temp fresh_temp raw in
    ( [ simplify_simple_instr
          (Tcg.Bin (quotient, Div, Tcg.Temp numer_temp, Tcg.Imm divisor));
        simplify_simple_instr
          (Tcg.Bin (remainder, Mod, Tcg.Temp numer_temp, Tcg.Imm divisor));
        simplify_simple_instr (Tcg.Bin (numer_pos, Gt, Tcg.Temp numer_temp, Tcg.Imm 0L));
        simplify_simple_instr (Tcg.Bin (rem_nz, Ne, Tcg.Temp remainder, Tcg.Imm 0L));
        simplify_simple_instr (Tcg.Bin (extra, Mul, Tcg.Temp numer_pos, Tcg.Temp rem_nz));
        simplify_simple_instr (Tcg.Bin (raw, Add, Tcg.Temp quotient, Tcg.Temp extra)) ]
      @ clamp_instrs,
      trip )

let build_nonnegative_inclusive_div fresh_temp numer_temp divisor =
  let floor_instrs, floor = build_floor_div fresh_temp numer_temp divisor in
  let raw = fresh_temp () in
  let clamp_instrs, trip = clamp_nonnegative_temp fresh_temp raw in
  ( floor_instrs
    @ [ simplify_simple_instr (Tcg.Bin (raw, Add, Tcg.Temp floor, Tcg.Imm 1L)) ]
    @ clamp_instrs,
    trip )

let build_trip_count_instrs fresh_temp phi_temp step kind =
  let adjust_bound bound bias =
    if bias = 0L then ([], bound)
    else
      match bound with
      | Tcg.Imm value -> ([], Tcg.Imm Int64.(sub value bias))
      | _ ->
          let adjusted = fresh_temp () in
          ([ simplify_simple_instr (Tcg.Bin (adjusted, Sub, bound, Tcg.Imm bias)) ], Tcg.Temp adjusted)
  in
  let stride = if step < 0L then Int64.neg step else step in
  let diff = fresh_temp () in
  match kind with
  | CountUpLt (bound, bias) ->
      let bound_instrs, bound = adjust_bound bound bias in
      let diff_instr = simplify_simple_instr (Tcg.Bin (diff, Sub, bound, Tcg.Temp phi_temp)) in
      let trip_instrs, trip = build_nonnegative_ceil_div fresh_temp diff stride in
      (bound_instrs @ (diff_instr :: trip_instrs), trip)
  | CountUpLe (bound, bias) ->
      let bound_instrs, bound = adjust_bound bound bias in
      let diff_instr = simplify_simple_instr (Tcg.Bin (diff, Sub, bound, Tcg.Temp phi_temp)) in
      let trip_instrs, trip = build_nonnegative_inclusive_div fresh_temp diff stride in
      (bound_instrs @ (diff_instr :: trip_instrs), trip)
  | CountDownGt (bound, bias) ->
      let bound_instrs, bound = adjust_bound bound bias in
      let diff_instr = simplify_simple_instr (Tcg.Bin (diff, Sub, Tcg.Temp phi_temp, bound)) in
      let trip_instrs, trip = build_nonnegative_ceil_div fresh_temp diff stride in
      (bound_instrs @ (diff_instr :: trip_instrs), trip)
  | CountDownGe (bound, bias) ->
      let bound_instrs, bound = adjust_bound bound bias in
      let diff_instr = simplify_simple_instr (Tcg.Bin (diff, Sub, Tcg.Temp phi_temp, bound)) in
      let trip_instrs, trip = build_nonnegative_inclusive_div fresh_temp diff stride in
      (bound_instrs @ (diff_instr :: trip_instrs), trip)

let int64_floor_div numer denom =
  let quotient = Int64.div numer denom in
  let remainder = Int64.rem numer denom in
  if numer < 0L && remainder <> 0L then Int64.pred quotient else quotient

let int64_nonnegative_ceil_div numer denom =
  if denom <= 0L then None
  else if numer <= 0L then Some 0L
  else
    let quotient = Int64.div numer denom in
    let remainder = Int64.rem numer denom in
    Some (if remainder = 0L then quotient else Int64.succ quotient)

let int64_nonnegative_inclusive_div numer denom =
  if denom <= 0L then None
  else
    let floor = int64_floor_div numer denom in
    Some (if floor < 0L then 0L else Int64.succ floor)

let constant_trip_count_of_kind resolve_operand init_value step = function
  | CountUpLt (bound, bias) -> (
      match resolve_operand bound with
      | Some bound ->
          int64_nonnegative_ceil_div Int64.(sub (sub bound bias) init_value) step
      | None -> None)
  | CountUpLe (bound, bias) -> (
      match resolve_operand bound with
      | Some bound ->
          int64_nonnegative_inclusive_div Int64.(sub (sub bound bias) init_value) step
      | None -> None)
  | CountDownGt (bound, bias) -> (
      match resolve_operand bound with
      | Some bound ->
          int64_nonnegative_ceil_div Int64.(sub init_value (sub bound bias)) (Int64.neg step)
      | None -> None)
  | CountDownGe (bound, bias) -> (
      match resolve_operand bound with
      | Some bound ->
          int64_nonnegative_inclusive_div Int64.(sub init_value (sub bound bias)) (Int64.neg step)
      | None -> None)

let build_iv_final_update fresh_temp trip_temp (iv : basic_induction_var) =
  match iv.step with
  | 0L -> []
  | 1L -> [ simplify_simple_instr (Tcg.Bin (iv.phi_temp, Add, Tcg.Temp iv.phi_temp, Tcg.Temp trip_temp)) ]
  | -1L -> [ simplify_simple_instr (Tcg.Bin (iv.phi_temp, Sub, Tcg.Temp iv.phi_temp, Tcg.Temp trip_temp)) ]
  | step ->
      let delta = fresh_temp () in
      [ simplify_simple_instr (Tcg.Bin (delta, Mul, Tcg.Temp trip_temp, Tcg.Imm step));
        simplify_simple_instr (Tcg.Bin (iv.phi_temp, Add, Tcg.Temp iv.phi_temp, Tcg.Temp delta)) ]

let counted_update_temp = function
  | CountedIv (iv : basic_induction_var) -> iv.phi_temp
  | CountedReduction { target = ReductionTempTarget temp; _ } -> temp
  | CountedReduction { target = ReductionPlaceTarget _; _ } -> invalid_arg "counted_update_temp"

let counted_update_place = function
  | CountedReduction { target = ReductionPlaceTarget place; _ } -> Some place
  | CountedIv _ | CountedReduction { target = ReductionTempTarget _; _ } -> None

let add_reduction_alias_temps acc (reduction : counted_reduction) =
  let acc =
    match reduction.carrier_temp with
    | Some temp -> IntSet.add temp acc
    | None -> acc
  in
  List.fold_left (fun acc temp -> IntSet.add temp acc) acc reduction.alias_temps

let place_carriers_of_reductions reductions =
  List.fold_left
    (fun acc (reduction : counted_reduction) ->
      match (reduction.target, reduction.carrier_temp) with
      | ReductionPlaceTarget place, Some temp -> PlaceMap.add place temp acc
      | ReductionTempTarget _, _ | ReductionPlaceTarget _, None -> acc)
    PlaceMap.empty reductions

let materialize_place_reduction_carriers fresh_temp reductions =
  let carriers = ref PlaceMap.empty in
  let preloads_rev = ref [] in
  let ensure_carrier place =
    match PlaceMap.find_opt place !carriers with
    | Some temp -> temp
    | None ->
        let temp = fresh_temp () in
        carriers := PlaceMap.add place temp !carriers;
        preloads_rev := simplify_simple_instr (Tcg.Load (temp, place)) :: !preloads_rev;
        temp
  in
  let reductions =
    List.map
      (fun (reduction : counted_reduction) ->
        match (reduction.target, reduction.carrier_temp) with
        | ReductionPlaceTarget place, None ->
            { reduction with carrier_temp = Some (ensure_carrier place) }
        | ReductionTempTarget _, _
        | ReductionPlaceTarget _, Some _ -> reduction)
      reductions
  in
  (reductions, List.rev !preloads_rev)

type linear_expr =
  | LinearInvariant of summary_expr
  | LinearAffine of {
      iv : basic_induction_var;
      coeff : summary_expr;
      bias : summary_expr;
    }

let zero_summary_expr = SummaryOperand (Tcg.Imm 0L)
let one_summary_expr = SummaryOperand (Tcg.Imm 1L)

let summary_expr_is_zero = function
  | SummaryOperand (Tcg.Imm 0L) -> true
  | SummaryOperand _ | SummaryPlace _ | SummaryUn _ | SummaryBin _ -> false

let summary_expr_is_one = function
  | SummaryOperand (Tcg.Imm 1L) -> true
  | SummaryOperand _ | SummaryPlace _ | SummaryUn _ | SummaryBin _ -> false

let summary_expr_is_minus_one = function
  | SummaryOperand (Tcg.Imm (-1L)) -> true
  | SummaryOperand _ | SummaryPlace _ | SummaryUn _ | SummaryBin _ -> false

let summary_expr_neg expr =
  if summary_expr_is_zero expr then expr else SummaryUn (UMinus, expr)

let summary_expr_add lhs rhs =
  if summary_expr_is_zero lhs then rhs
  else if summary_expr_is_zero rhs then lhs
  else SummaryBin (Add, lhs, rhs)

let summary_expr_sub lhs rhs =
  if summary_expr_is_zero rhs then lhs
  else if summary_expr_is_zero lhs then summary_expr_neg rhs
  else SummaryBin (Sub, lhs, rhs)

let summary_expr_mul lhs rhs =
  if summary_expr_is_zero lhs || summary_expr_is_zero rhs then zero_summary_expr
  else if summary_expr_is_one lhs then rhs
  else if summary_expr_is_one rhs then lhs
  else if summary_expr_is_minus_one lhs then summary_expr_neg rhs
  else if summary_expr_is_minus_one rhs then summary_expr_neg lhs
  else SummaryBin (Mul, lhs, rhs)

let linear_affine iv coeff bias =
  if summary_expr_is_zero coeff then LinearInvariant bias else LinearAffine { iv; coeff; bias }

let linear_expr_neg = function
  | LinearInvariant expr -> LinearInvariant (summary_expr_neg expr)
  | LinearAffine { iv; coeff; bias } ->
      linear_affine iv (summary_expr_neg coeff) (summary_expr_neg bias)

let linear_expr_add lhs rhs =
  match (lhs, rhs) with
  | LinearInvariant lhs, LinearInvariant rhs -> Some (LinearInvariant (summary_expr_add lhs rhs))
  | LinearAffine { iv; coeff; bias }, LinearInvariant rhs
  | LinearInvariant rhs, LinearAffine { iv; coeff; bias } ->
      Some (linear_affine iv coeff (summary_expr_add bias rhs))
  | LinearAffine lhs, LinearAffine rhs when lhs.iv.phi_temp = rhs.iv.phi_temp ->
      Some (linear_affine lhs.iv (summary_expr_add lhs.coeff rhs.coeff) (summary_expr_add lhs.bias rhs.bias))
  | LinearAffine _, LinearAffine _ -> None

let linear_expr_sub lhs rhs =
  match (lhs, rhs) with
  | LinearInvariant lhs, LinearInvariant rhs -> Some (LinearInvariant (summary_expr_sub lhs rhs))
  | LinearAffine { iv; coeff; bias }, LinearInvariant rhs ->
      Some (linear_affine iv coeff (summary_expr_sub bias rhs))
  | LinearInvariant lhs, LinearAffine { iv; coeff; bias } ->
      Some (linear_affine iv (summary_expr_neg coeff) (summary_expr_sub lhs bias))
  | LinearAffine lhs, LinearAffine rhs when lhs.iv.phi_temp = rhs.iv.phi_temp ->
      Some (linear_affine lhs.iv (summary_expr_sub lhs.coeff rhs.coeff) (summary_expr_sub lhs.bias rhs.bias))
  | LinearAffine _, LinearAffine _ -> None

let linear_expr_mul_invariant factor = function
  | LinearInvariant expr -> Some (LinearInvariant (summary_expr_mul factor expr))
  | LinearAffine { iv; coeff; bias } ->
      Some (linear_affine iv (summary_expr_mul factor coeff) (summary_expr_mul factor bias))

let summary_expr_of_operand_with_bases
    base_temps
    invariant_loaded_places
    loop_defs
    def_blocks
    get_block
    loop_stable_phis
    multi_defs
    def_instrs
    (block : Cfg.block)
    operand
  =
  let invariant operand =
    operand_loop_invariant
      loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty operand
  in
  let rec of_operand block seen = function
    | Tcg.Imm _ as operand -> Some (SummaryOperand operand)
    | Tcg.Temp temp as operand ->
        if IntSet.mem temp base_temps || invariant operand then Some (SummaryOperand operand)
        else if IntSet.mem temp seen || IntSet.mem temp multi_defs then None
        else
          match last_def_of_temp block temp with
          | Some instr -> of_instr block (IntSet.add temp seen) instr
          | None -> (
              match Hashtbl.find_opt def_instrs temp with
              | Some instr -> (
                  match Hashtbl.find_opt def_blocks temp with
                  | Some label -> of_instr (get_block label) (IntSet.add temp seen) instr
                  | None -> None)
              | None -> None)
  and of_instr block seen = function
    | Tcg.Move (_, src) -> of_operand block seen (resolve_block_operand block src)
    | Tcg.Load (_, place) when PlaceSet.mem place invariant_loaded_places ->
        Some (SummaryPlace place)
    | Tcg.Un (_, op, src) ->
        let src = resolve_block_operand block src in
        Option.map (fun src -> SummaryUn (op, src)) (of_operand block seen src)
    | Tcg.Bin (_, Add, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        Option.bind (of_operand block seen lhs) (fun lhs ->
            Option.map (fun rhs -> SummaryBin (Add, lhs, rhs)) (of_operand block seen rhs))
    | Tcg.Bin (_, Sub, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        Option.bind (of_operand block seen lhs) (fun lhs ->
            Option.map (fun rhs -> SummaryBin (Sub, lhs, rhs)) (of_operand block seen rhs))
    | Tcg.Bin (_, op, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        Option.bind (of_operand block seen lhs) (fun lhs ->
            Option.map (fun rhs -> SummaryBin (op, lhs, rhs)) (of_operand block seen rhs))
    | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> None
  in
  of_operand block IntSet.empty operand

let summary_expr_of_operand
    invariant_loaded_places
    loop_defs
    def_blocks
    get_block
    loop_stable_phis
    multi_defs
    def_instrs
    (block : Cfg.block)
    operand
  =
  summary_expr_of_operand_with_bases
    IntSet.empty
    invariant_loaded_places
    loop_defs
    def_blocks
    get_block
    loop_stable_phis
    multi_defs
    def_instrs
    block
    operand

let linear_expr_of_operand
    invariant_loaded_places
    loop_defs
    def_blocks
    get_block
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    (block : Cfg.block)
    operand
  =
  let direct_scaled operand =
    let operand = resolve_block_operand block operand in
    List.find_map
      (fun (iv : basic_induction_var) ->
        if resolves_to_induction_temp multi_defs def_instrs iv.phi_temp operand then
          Some (LinearAffine { iv; coeff = one_summary_expr; bias = zero_summary_expr })
        else None)
      ivs
  in
  let rec of_operand block seen operand =
    match direct_scaled operand with
    | Some expr -> Some expr
    | None -> (
        match
          summary_expr_of_operand
            invariant_loaded_places
            loop_defs def_blocks get_block loop_stable_phis multi_defs def_instrs block operand
        with
        | Some expr -> Some (LinearInvariant expr)
        | None -> (
            match operand with
            | Tcg.Imm _ -> None
            | Tcg.Temp temp ->
                if IntSet.mem temp seen || IntSet.mem temp multi_defs then None
                else
                  match last_def_of_temp block temp with
                  | Some instr -> of_instr block (IntSet.add temp seen) instr
                  | None -> (
                      match Hashtbl.find_opt def_instrs temp with
                      | Some instr -> (
                          match Hashtbl.find_opt def_blocks temp with
                          | Some label -> of_instr (get_block label) (IntSet.add temp seen) instr
                          | None -> None)
                      | None -> None)))
  and of_instr block seen = function
    | Tcg.Move (_, src) -> of_operand block seen (resolve_block_operand block src)
    | Tcg.Un (_, UMinus, src) ->
        let src = resolve_block_operand block src in
        Option.map linear_expr_neg (of_operand block seen src)
    | Tcg.Un _ -> None
    | Tcg.Bin (_, Add, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        Option.bind (of_operand block seen lhs) (fun lhs ->
            Option.bind (of_operand block seen rhs) (linear_expr_add lhs))
    | Tcg.Bin (_, Sub, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        Option.bind (of_operand block seen lhs) (fun lhs ->
            Option.bind (of_operand block seen rhs) (linear_expr_sub lhs))
    | Tcg.Bin (_, Mul, lhs, rhs) -> (
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        match
          ( summary_expr_of_operand
              invariant_loaded_places
              loop_defs def_blocks get_block loop_stable_phis multi_defs def_instrs block lhs,
            of_operand block seen rhs,
            summary_expr_of_operand
              invariant_loaded_places
              loop_defs def_blocks get_block loop_stable_phis multi_defs def_instrs block rhs,
            of_operand block seen lhs )
        with
        | Some factor, Some rhs_expr, _, _ -> linear_expr_mul_invariant factor rhs_expr
        | _, _, Some factor, Some lhs_expr -> linear_expr_mul_invariant factor lhs_expr
        | _ -> None)
    | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> None
  in
  of_operand block IntSet.empty operand

let reduction_step_of_operand
    invariant_loaded_places
    loop_defs
    def_blocks
    get_block
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    (block : Cfg.block)
    operand
  =
  match
    linear_expr_of_operand
      invariant_loaded_places
      loop_defs def_blocks get_block loop_stable_phis multi_defs def_instrs ivs block operand
  with
  | Some (LinearInvariant expr) -> Some (ReductionInvariant expr)
  | Some (LinearAffine { iv; coeff; bias }) when not (summary_expr_is_zero coeff) ->
      Some (ReductionAffine { iv; coeff; bias })
  | Some (LinearAffine _) -> None
  | None -> None

let reduction_update_of_temp
    invariant_loaded_places
    loop_defs
    def_blocks
    get_block
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    phi_temp
    (block : Cfg.block)
    temp
  =
  let invariant operand =
    operand_loop_invariant
      loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty operand
  in
  let rec of_operand block seen = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp as operand ->
        if temp = phi_temp then None
        else if IntSet.mem temp seen || IntSet.mem temp multi_defs then None
        else
          match last_def_of_temp block temp with
          | Some instr -> of_instr block (IntSet.add temp seen) instr
          | None ->
              if invariant operand then None
              else
                match Hashtbl.find_opt def_instrs temp with
                | Some instr -> (
                    match Hashtbl.find_opt def_blocks temp with
                    | Some label -> of_instr (get_block label) (IntSet.add temp seen) instr
                    | None -> None)
                | None -> None
  and of_instr block seen = function
    | Tcg.Move (_, src) -> of_operand block seen (resolve_block_operand block src)
    | Tcg.Bin (_, Add, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        if resolves_to_induction_temp multi_defs def_instrs phi_temp lhs then
          Option.map
            (fun step ->
              {
                target = ReductionTempTarget phi_temp;
                subtract = false;
                step;
                carrier_temp = None;
                alias_temps = [];
              })
            (reduction_step_of_operand
               invariant_loaded_places
               loop_defs
               def_blocks
               get_block
               loop_stable_phis
               multi_defs
               def_instrs
               ivs
               block rhs)
        else if resolves_to_induction_temp multi_defs def_instrs phi_temp rhs then
          Option.map
            (fun step ->
              {
                target = ReductionTempTarget phi_temp;
                subtract = false;
                step;
                carrier_temp = None;
                alias_temps = [];
              })
            (reduction_step_of_operand
               invariant_loaded_places
               loop_defs
               def_blocks
               get_block
               loop_stable_phis
               multi_defs
               def_instrs
               ivs
               block lhs)
        else None
    | Tcg.Bin (_, Sub, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        if resolves_to_induction_temp multi_defs def_instrs phi_temp lhs then
          Option.map
            (fun step ->
              {
                target = ReductionTempTarget phi_temp;
                subtract = true;
                step;
                carrier_temp = None;
                alias_temps = [];
              })
            (reduction_step_of_operand
               invariant_loaded_places
               loop_defs
               def_blocks
               get_block
               loop_stable_phis
               multi_defs
               def_instrs
               ivs
               block rhs)
        else None
    | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ | Tcg.Bin _ -> None
  in
  match last_def_of_temp block temp with
  | Some (Tcg.Move (_, src)) -> of_operand block IntSet.empty (resolve_block_operand block src)
  | Some instr -> of_instr block IntSet.empty instr
  | None -> of_operand block IntSet.empty (Tcg.Temp temp)

let rec operand_resolves_to_place_value multi_defs place (block : Cfg.block) seen = function
  | Tcg.Imm _ -> false
  | Tcg.Temp _ as operand ->
      let operand = resolve_block_operand block operand in
      (match operand with
      | Tcg.Imm _ -> false
      | Tcg.Temp temp ->
          if IntSet.mem temp seen || IntSet.mem temp multi_defs then false
          else
            match last_def_of_temp block temp with
            | Some (Tcg.Load (_, loaded_place)) -> loaded_place = place
            | Some (Tcg.Move (_, src)) ->
                operand_resolves_to_place_value multi_defs place block (IntSet.add temp seen) src
            | Some _ | None -> false)

let last_store_of_place place (block : Cfg.block) =
  let last = ref None in
  List.iteri
    (fun index instr ->
      match instr with
      | Tcg.Store (stored_place, value) when stored_place = place -> last := Some (index, value)
      | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> ())
    block.body;
  !last

let reduction_update_of_place
    invariant_loaded_places
    loop_defs
    def_blocks
    get_block
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    place
    (block : Cfg.block)
  =
  let rec of_operand block seen = function
    | Tcg.Imm _ -> None
    | Tcg.Temp _ as operand ->
        let operand = resolve_block_operand block operand in
        (match operand with
        | Tcg.Imm _ -> None
        | Tcg.Temp temp ->
            if IntSet.mem temp seen || IntSet.mem temp multi_defs then None
            else
              match last_def_of_temp block temp with
              | Some (Tcg.Move (_, src)) -> of_operand block (IntSet.add temp seen) src
              | Some instr -> of_instr block (IntSet.add temp seen) instr
              | None -> None)
  and of_instr block seen = function
    | Tcg.Move (_, src) -> of_operand block seen (resolve_block_operand block src)
    | Tcg.Bin (_, Add, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        if operand_resolves_to_place_value multi_defs place block IntSet.empty lhs then
          Option.map
            (fun step ->
              {
                target = ReductionPlaceTarget place;
                subtract = false;
                step;
                carrier_temp = None;
                alias_temps = [];
              })
            (reduction_step_of_operand
               invariant_loaded_places
               loop_defs
               def_blocks
               get_block
               loop_stable_phis
               multi_defs
               def_instrs
               ivs
               block rhs)
        else if operand_resolves_to_place_value multi_defs place block IntSet.empty rhs then
          Option.map
            (fun step ->
              {
                target = ReductionPlaceTarget place;
                subtract = false;
                step;
                carrier_temp = None;
                alias_temps = [];
              })
            (reduction_step_of_operand
               invariant_loaded_places
               loop_defs
               def_blocks
               get_block
               loop_stable_phis
               multi_defs
               def_instrs
               ivs
               block lhs)
        else None
    | Tcg.Bin (_, Sub, lhs, rhs) ->
        let lhs = resolve_block_operand block lhs in
        let rhs = resolve_block_operand block rhs in
        if operand_resolves_to_place_value multi_defs place block IntSet.empty lhs then
          Option.map
            (fun step ->
              {
                target = ReductionPlaceTarget place;
                subtract = true;
                step;
                carrier_temp = None;
                alias_temps = [];
              })
            (reduction_step_of_operand
               invariant_loaded_places
               loop_defs
               def_blocks
               get_block
               loop_stable_phis
               multi_defs
               def_instrs
               ivs
               block rhs)
        else None
    | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ | Tcg.Bin _ -> None
  in
  match last_store_of_place place block with
  | Some (_, value) -> of_operand block IntSet.empty value
  | None -> None

let collect_counted_reductions
    header
    loop
    invariant_loaded_places
    loop_defs
    get_block
    def_blocks
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    excluded_temps
    live_temps
    live_places
  =
  let debug_counted_local = Sys.getenv_opt "TOYC_DEBUG_COUNTED_LOOPS" <> None in
  let string_of_temps set =
    IntSet.elements set |> List.map string_of_int |> String.concat ","
  in
  let string_of_operand = function
    | Tcg.Imm n -> Int64.to_string n
    | Tcg.Temp t -> Printf.sprintf "t%d" t
  in
  let string_of_binop = function
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | Div -> "div"
    | Mod -> "mod"
    | Lt -> "lt"
    | Le -> "le"
    | Gt -> "gt"
    | Ge -> "ge"
    | Eq -> "eq"
    | Ne -> "ne"
    | LAnd -> "land"
    | LOr -> "lor"
  in
  let string_of_unop = function
    | UMinus -> "uminus"
    | UNot -> "unot"
    | UPlus -> "uplus"
  in
  let debug_operand_def operand =
    match operand with
    | Tcg.Imm _ -> "imm"
    | Tcg.Temp temp -> (
        match Hashtbl.find_opt def_instrs temp with
        | Some (Tcg.Move (_, src)) -> Printf.sprintf "move(%s)" (string_of_operand src)
        | Some (Tcg.Un (_, op, src)) ->
            Printf.sprintf "%s(%s)" (string_of_unop op) (string_of_operand src)
        | Some (Tcg.Bin (_, op, lhs, rhs)) ->
            Printf.sprintf "%s(%s,%s)" (string_of_binop op) (string_of_operand lhs)
              (string_of_operand rhs)
        | Some (Tcg.Load _) -> "load"
        | Some (Tcg.Store _) -> "store"
        | Some (Tcg.Call _) -> "call"
        | None -> "none")
  in
  let header_block : Cfg.block = get_block header in
  let outside_preds = List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds in
  let backedge_preds = List.filter (fun pred -> LabelSet.mem pred loop) header_block.preds in
  let phi_chain_for_pred pred = incoming_phi_chain get_block header pred in
  let update_chain_for_pred pred =
    if LabelSet.mem pred loop then incoming_update_chain get_block header pred
    else phi_chain_for_pred pred
  in
  let resolve_on_update_chain block older_chain operand =
    resolve_chain_operand (block :: older_chain) (resolve_block_operand block operand)
  in
  let agree_all = function
    | [] -> None
    | first :: rest -> if List.for_all (( = ) first) rest then Some first else None
  in
  let anchor_iv =
    match List.filter (fun (iv : basic_induction_var) -> Int64.abs iv.step = 1L) ivs with
    | [ iv ] -> Some iv
    | _ -> None
  in
  let expand_chain_move_aliases chain initial =
    let rec saturate seen =
      let next =
        List.fold_left
          (fun seen (block : Cfg.block) ->
            List.fold_left
              (fun seen instr ->
                match instr with
                | Tcg.Move (dst, Tcg.Temp src)
                | Tcg.Un (dst, UPlus, Tcg.Temp src) when IntSet.mem src seen -> IntSet.add dst seen
                | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> seen)
              seen block.body)
          seen chain
      in
      if IntSet.equal next seen then seen else saturate next
    in
    saturate initial
  in
  let self_temps_on_chain seed_temp chain =
    let rec collect seen = function
      | [] -> seen
      | current :: rest when IntSet.mem current seen -> collect seen rest
      | current :: rest ->
          let seen = IntSet.add current seen in
          let pushed =
            match def_instr_on_chain_or_global chain multi_defs def_instrs current with
            | Some (Tcg.Move (_, Tcg.Temp src))
            | Some (Tcg.Un (_, UPlus, Tcg.Temp src)) ->
                src :: rest
            | Some _ | None -> rest
          in
          collect seen pushed
    in
    collect IntSet.empty [ seed_temp ] |> expand_chain_move_aliases chain
  in
  let direct_simple_invariant_reduction_of_temp_on_chain source_temp chain =
    let self_temps = self_temps_on_chain source_temp chain in
    let rec resolves_to_self block older_chain seen operand =
      let operand = resolve_on_update_chain block older_chain operand in
      match operand with
      | Tcg.Imm _ -> false
      | Tcg.Temp current ->
          if IntSet.mem current self_temps then true
          else if IntSet.mem current seen then false
          else
            match last_def_of_temp block current with
            | Some (Tcg.Move (_, src))
            | Some (Tcg.Un (_, UPlus, src)) ->
                resolves_to_self block older_chain (IntSet.add current seen) src
            | Some _ -> false
            | None -> (
                match last_def_of_temp_on_chain_with_block older_chain current with
                | Some (older_block, Tcg.Move (_, src), older_rest)
                | Some (older_block, Tcg.Un (_, UPlus, src), older_rest) ->
                    resolves_to_self older_block older_rest (IntSet.add current seen) src
                | Some _ | None -> false)
    in
    let rec of_operand block older_chain seen = function
      | Tcg.Imm _ -> None
      | Tcg.Temp _ as operand ->
          let operand = resolve_on_update_chain block older_chain operand in
          (match operand with
          | Tcg.Imm _ -> None
          | Tcg.Temp current ->
              if IntSet.mem current seen || IntSet.mem current multi_defs then None
              else
                match last_def_of_temp block current with
                | Some instr -> of_instr block older_chain (IntSet.add current seen) instr
                | None -> (
                    match last_def_of_temp_on_chain_with_block older_chain current with
                    | Some (older_block, instr, older_rest) ->
                        of_instr older_block older_rest (IntSet.add current seen) instr
                    | None -> None))
    and of_instr block older_chain seen = function
      | Tcg.Move (_, src) -> of_operand block older_chain seen (resolve_on_update_chain block older_chain src)
      | Tcg.Bin (_, Add, lhs, rhs) ->
          let lhs = resolve_on_update_chain block older_chain lhs in
          let rhs = resolve_on_update_chain block older_chain rhs in
          if resolves_to_self block older_chain IntSet.empty lhs then
            Option.bind
              (summary_expr_of_operand
                 invariant_loaded_places
                 loop_defs
                 def_blocks
                 get_block
                 loop_stable_phis
                 multi_defs
                 def_instrs
                 block
                 rhs)
              (function
                | SummaryOperand (Tcg.Imm 0L) -> None
                | step_expr ->
                    Some
                      {
                        target = ReductionTempTarget source_temp;
                        subtract = false;
                        step = ReductionInvariant step_expr;
                        carrier_temp = None;
                        alias_temps = [];
                      })
          else if resolves_to_self block older_chain IntSet.empty rhs then
            Option.bind
              (summary_expr_of_operand
                 invariant_loaded_places
                 loop_defs
                 def_blocks
                 get_block
                 loop_stable_phis
                 multi_defs
                 def_instrs
                 block
                 lhs)
              (function
                | SummaryOperand (Tcg.Imm 0L) -> None
                | step_expr ->
                    Some
                      {
                        target = ReductionTempTarget source_temp;
                        subtract = false;
                        step = ReductionInvariant step_expr;
                        carrier_temp = None;
                        alias_temps = [];
                      })
          else None
      | Tcg.Bin (_, Sub, lhs, rhs) ->
          let lhs = resolve_on_update_chain block older_chain lhs in
          let rhs = resolve_on_update_chain block older_chain rhs in
          if resolves_to_self block older_chain IntSet.empty lhs then
            Option.bind
              (summary_expr_of_operand
                 invariant_loaded_places
                 loop_defs
                 def_blocks
                 get_block
                 loop_stable_phis
                 multi_defs
                 def_instrs
                 block
                 rhs)
              (function
                | SummaryOperand (Tcg.Imm 0L) -> None
                | step_expr ->
                    Some
                      {
                        target = ReductionTempTarget source_temp;
                        subtract = true;
                        step = ReductionInvariant step_expr;
                        carrier_temp = None;
                        alias_temps = [];
                      })
          else None
      | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ | Tcg.Bin _ -> None
    in
    match last_def_of_temp_on_chain_with_block chain source_temp with
    | Some (block, Tcg.Move (_, src), older_chain) ->
        of_operand block older_chain IntSet.empty (resolve_on_update_chain block older_chain src)
    | Some (block, instr, older_chain) -> of_instr block older_chain IntSet.empty instr
    | None -> None
  in
  let carrier_progression_of_operand block older_chain operand =
    let rec of_operand block older_chain seen = function
      | Tcg.Imm _ -> None
      | Tcg.Temp _ as operand ->
          let operand = resolve_on_update_chain block older_chain operand in
          (match operand with
          | Tcg.Imm _ -> None
          | Tcg.Temp current ->
              if debug_counted_local then
                Printf.eprintf
                  "counted-carrier-of-operand header=%s current=t%d def=%s seen=%b\n%!"
                  header current (debug_operand_def (Tcg.Temp current)) (IntSet.mem current seen);
              if IntSet.mem current seen then None
              else
                match last_def_of_temp block current with
                | Some (Tcg.Move (_, src))
                | Some (Tcg.Un (_, UPlus, src)) ->
                    of_operand block older_chain (IntSet.add current seen) src
                | Some instr -> of_instr block older_chain (IntSet.add current seen) instr
                | None -> (
                    match last_def_of_temp_on_chain_with_block older_chain current with
                    | Some (older_block, Tcg.Move (_, src), older_rest)
                    | Some (older_block, Tcg.Un (_, UPlus, src), older_rest) ->
                        of_operand older_block older_rest (IntSet.add current seen) src
                    | Some (older_block, instr, older_rest) ->
                        of_instr older_block older_rest (IntSet.add current seen) instr
                    | None -> (
                        match older_chain with
                        | (join_block : Cfg.block) :: _
                          when List.length join_block.preds > 1 ->
                            let pred_results =
                              List.map
                                (fun pred ->
                                  let pred_chain = incoming_update_chain get_block join_block.label pred in
                                  match last_def_of_temp_on_chain_with_block pred_chain current with
                                  | Some (pred_block, Tcg.Move (_, src), pred_rest)
                                  | Some (pred_block, Tcg.Un (_, UPlus, src), pred_rest) ->
                                      of_operand pred_block pred_rest (IntSet.add current seen) src
                                  | Some (pred_block, instr, pred_rest) ->
                                      of_instr pred_block pred_rest (IntSet.add current seen) instr
                                  | None -> None)
                                join_block.preds
                            in
                            Option.value (agree_all pred_results) ~default:None
                        | _ -> (
                            match Hashtbl.find_opt def_instrs current with
                            | Some instr -> (
                                match Hashtbl.find_opt def_blocks current with
                                | Some label -> (
                                    match chain_rest_from_label older_chain label with
                                    | Some (def_block, older_rest) ->
                                        of_instr def_block older_rest (IntSet.add current seen) instr
                                    | None -> of_instr (get_block label) [] (IntSet.add current seen) instr)
                                | None -> None)
                            | None -> None))))
    and of_instr block _older_chain _seen = function
      | Tcg.Bin (_, Add, lhs, rhs) -> (
          let lhs = resolve_on_update_chain block older_chain lhs in
          let rhs = resolve_on_update_chain block older_chain rhs in
          if debug_counted_local then
            Printf.eprintf
              "counted-carrier-try header=%s add lhs=%s rhs=%s\n%!"
              header (string_of_operand lhs) (string_of_operand rhs);
          match (lhs, rhs) with
          | Tcg.Temp carrier_temp, _ when Option.is_some (summary_expr_of_operand
                                        invariant_loaded_places
                                        loop_defs
                                        def_blocks
                                        get_block
                                        loop_stable_phis
                                        multi_defs
                                        def_instrs
                                        block
                                        rhs) ->
              Option.map
                (fun step_expr -> (carrier_temp, step_expr, false, true))
                (summary_expr_of_operand
                   invariant_loaded_places
                   loop_defs
                   def_blocks
                   get_block
                   loop_stable_phis
                   multi_defs
                   def_instrs
                   block
                   rhs)
          | _, Tcg.Temp carrier_temp when Option.is_some (summary_expr_of_operand
                                        invariant_loaded_places
                                        loop_defs
                                        def_blocks
                                        get_block
                                        loop_stable_phis
                                        multi_defs
                                        def_instrs
                                        block
                                        lhs) ->
              Option.map
                (fun step_expr -> (carrier_temp, step_expr, false, true))
                (summary_expr_of_operand
                   invariant_loaded_places
                   loop_defs
                   def_blocks
                   get_block
                   loop_stable_phis
                   multi_defs
                   def_instrs
                   block
                   lhs)
          | _ ->
              if debug_counted_local then
                Printf.eprintf "counted-carrier-miss header=%s add\n%!" header;
              None)
      | Tcg.Bin (_, Sub, lhs, rhs) -> (
          let lhs = resolve_on_update_chain block older_chain lhs in
          let rhs = resolve_on_update_chain block older_chain rhs in
          if debug_counted_local then
            Printf.eprintf
              "counted-carrier-try header=%s sub lhs=%s rhs=%s\n%!"
              header (string_of_operand lhs) (string_of_operand rhs);
          match (lhs, rhs) with
          | Tcg.Temp carrier_temp, _ ->
              Option.map
                (fun step_expr -> (carrier_temp, step_expr, true, true))
                (summary_expr_of_operand
                   invariant_loaded_places
                   loop_defs
                   def_blocks
                   get_block
                   loop_stable_phis
                   multi_defs
                   def_instrs
                   block
                   rhs)
          | _ ->
              if debug_counted_local then
                Printf.eprintf "counted-carrier-miss header=%s sub\n%!" header;
              None)
      | Tcg.Move _ | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ | Tcg.Bin _ -> None
    in
    of_operand block older_chain IntSet.empty operand
  in
  let dependent_affine_step_of_operand block older_chain operand =
    match anchor_iv with
    | None -> None
    | Some anchor_iv -> (
        match resolve_on_update_chain block older_chain operand with
        | Tcg.Imm _ -> None
        | Tcg.Temp source_temp ->
            if IntSet.mem source_temp excluded_temps then None
            else if
              not
                (List.for_all
                   (fun pred -> Option.is_some (last_def_of_temp_on_chain (phi_chain_for_pred pred) source_temp))
                   outside_preds)
            then None
            else
              match direct_simple_invariant_reduction_of_temp_on_chain source_temp older_chain with
              | Some
                  {
                    target = ReductionTempTarget _;
                    subtract = source_subtract;
                    step = ReductionInvariant source_step;
                    _;
                  } ->
                  let coeff =
                    let coeff = if source_subtract then summary_expr_neg source_step else source_step in
                    if anchor_iv.step < 0L then summary_expr_neg coeff else coeff
                  in
                  let source_current = SummaryOperand (Tcg.Temp source_temp) in
                  let iv_current = SummaryOperand (Tcg.Temp anchor_iv.phi_temp) in
                  let bias = summary_expr_sub source_current (summary_expr_mul coeff iv_current) in
                  Some (anchor_iv, coeff, bias)
              | Some _ | None -> None)
  in
  let reduction_update_of_temp_on_chain temp chain =
    let self_temps = self_temps_on_chain temp chain in
    let rec resolves_to_self block older_chain seen operand =
      let operand = resolve_on_update_chain block older_chain operand in
      match operand with
      | Tcg.Imm _ -> false
      | Tcg.Temp current ->
          if IntSet.mem current self_temps then true
          else if IntSet.mem current seen then false
          else
            match last_def_of_temp block current with
            | Some (Tcg.Move (_, src))
            | Some (Tcg.Un (_, UPlus, src)) ->
                resolves_to_self block older_chain (IntSet.add current seen) src
            | Some _ -> false
            | None -> (
                match last_def_of_temp_on_chain_with_block older_chain current with
                | Some (older_block, Tcg.Move (_, src), older_rest)
                | Some (older_block, Tcg.Un (_, UPlus, src), older_rest) ->
                    resolves_to_self older_block older_rest (IntSet.add current seen) src
                | Some _ | None -> false)
    in
    let rec peel_self_delta block older_chain seen = function
      | Tcg.Imm _ -> None
      | Tcg.Temp _ as operand -> (
          let operand = resolve_on_update_chain block older_chain operand in
          match operand with
          | Tcg.Imm _ -> None
          | Tcg.Temp current ->
              if IntSet.mem current seen then None
              else
                match last_def_of_temp block current with
                | Some (Tcg.Move (_, src))
                | Some (Tcg.Un (_, UPlus, src)) ->
                    peel_self_delta block older_chain (IntSet.add current seen) src
                | Some (Tcg.Bin (_, Add, lhs, rhs)) ->
                    let lhs = resolve_on_update_chain block older_chain lhs in
                    let rhs = resolve_on_update_chain block older_chain rhs in
                    if resolves_to_self block older_chain IntSet.empty lhs then Some rhs
                    else if resolves_to_self block older_chain IntSet.empty rhs then Some lhs
                    else None
                | Some instr -> (
                    match instr with
                    | Tcg.Move _ | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ | Tcg.Bin _ ->
                        None)
                | None -> (
                    match last_def_of_temp_on_chain_with_block older_chain current with
                    | Some (older_block, Tcg.Move (_, src), older_rest)
                    | Some (older_block, Tcg.Un (_, UPlus, src), older_rest) ->
                        peel_self_delta older_block older_rest (IntSet.add current seen) src
                    | Some (older_block, Tcg.Bin (_, Add, lhs, rhs), older_rest) ->
                        let lhs = resolve_on_update_chain older_block older_rest lhs in
                        let rhs = resolve_on_update_chain older_block older_rest rhs in
                        if resolves_to_self older_block older_rest IntSet.empty lhs then Some rhs
                        else if resolves_to_self older_block older_rest IntSet.empty rhs then Some lhs
                        else None
                    | Some _ -> None
                    | None -> (
                        match older_chain with
                        | (join_block : Cfg.block) :: _
                          when List.length join_block.preds > 1 -> (
                            let pred_results =
                              List.map
                                (fun pred ->
                                  let pred_chain = incoming_update_chain get_block join_block.label pred in
                                  match last_def_of_temp_on_chain_with_block pred_chain current with
                                  | Some (pred_block, Tcg.Move (_, src), pred_rest)
                                  | Some (pred_block, Tcg.Un (_, UPlus, src), pred_rest) ->
                                      peel_self_delta pred_block pred_rest (IntSet.add current seen) src
                                  | Some (pred_block, Tcg.Bin (_, Add, lhs, rhs), pred_rest) ->
                                      let lhs = resolve_on_update_chain pred_block pred_rest lhs in
                                      let rhs = resolve_on_update_chain pred_block pred_rest rhs in
                                      if resolves_to_self pred_block pred_rest IntSet.empty lhs then Some rhs
                                      else if resolves_to_self pred_block pred_rest IntSet.empty rhs then Some lhs
                                      else None
                                  | Some _ | None -> None)
                                join_block.preds
                            in
                            Option.value (agree_all pred_results) ~default:None)
                        | _ ->
                            (match Hashtbl.find_opt def_instrs current with
                            | Some (Tcg.Move (_, src))
                            | Some (Tcg.Un (_, UPlus, src)) -> (
                                match Hashtbl.find_opt def_blocks current with
                                | Some label -> (
                                    match chain_rest_from_label older_chain label with
                                    | Some (def_block, older_rest) ->
                                        peel_self_delta def_block older_rest (IntSet.add current seen) src
                                    | None ->
                                        peel_self_delta (get_block label) [] (IntSet.add current seen) src)
                                | None -> None)
                            | Some (Tcg.Bin (_, Add, lhs, rhs)) -> (
                                match Hashtbl.find_opt def_blocks current with
                                | Some label ->
                                    let def_block =
                                      match chain_rest_from_label older_chain label with
                                      | Some (def_block, _) -> def_block
                                      | None -> get_block label
                                    in
                                    let lhs = resolve_on_update_chain def_block [] lhs in
                                    let rhs = resolve_on_update_chain def_block [] rhs in
                                    if resolves_to_self def_block [] IntSet.empty lhs then Some rhs
                                    else if resolves_to_self def_block [] IntSet.empty rhs then Some lhs
                                    else None
                                | None -> None)
                            | Some _ | None -> None))))
    in
    let invariant operand =
      operand_loop_invariant
        loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty operand
    in
    let rec of_operand block older_chain seen = function
      | Tcg.Imm _ -> None
      | Tcg.Temp _ as operand ->
          let operand = resolve_on_update_chain block older_chain operand in
          match operand with
          | Tcg.Imm _ -> None
          | Tcg.Temp current ->
              if current = temp then None
              else if IntSet.mem current seen || IntSet.mem current multi_defs then None
              else
                match last_def_of_temp block current with
                | Some instr -> of_instr block older_chain (IntSet.add current seen) instr
                | None -> (
                    match last_def_of_temp_on_chain_with_block older_chain current with
                    | Some (older_block, instr, older_rest) ->
                        of_instr older_block older_rest (IntSet.add current seen) instr
                    | None ->
                        if invariant operand then None
                        else
                          match Hashtbl.find_opt def_instrs current with
                          | Some instr -> (
                              match Hashtbl.find_opt def_blocks current with
                              | Some label -> (
                                  match chain_rest_from_label older_chain label with
                                  | Some (def_block, older_rest) ->
                                      of_instr def_block older_rest (IntSet.add current seen) instr
                                  | None -> of_instr (get_block label) [] (IntSet.add current seen) instr)
                              | None -> None)
                          | None -> None)
    and of_instr block older_chain seen = function
      | Tcg.Move (_, src) -> of_operand block older_chain seen (resolve_on_update_chain block older_chain src)
      | Tcg.Bin (_, Add, lhs, rhs) ->
          let lhs = resolve_on_update_chain block older_chain lhs in
          let rhs = resolve_on_update_chain block older_chain rhs in
          if resolves_to_self block older_chain IntSet.empty lhs then (
            if debug_counted_local then
              Printf.eprintf
                "counted-self-hit header=%s temp=%d side=lhs other=%s self={%s}\n%!"
                header temp
                (Printf.sprintf "%s/%s" (string_of_operand rhs) (debug_operand_def rhs))
                (string_of_temps self_temps);
            match
              reduction_step_of_operand
                invariant_loaded_places
                loop_defs
                def_blocks
                get_block
                loop_stable_phis
                multi_defs
                def_instrs
                ivs
                block rhs
            with
            | Some step ->
                Some
                  {
                    target = ReductionTempTarget temp;
                    subtract = false;
                    step;
                    carrier_temp = None;
                    alias_temps = [];
                  }
             | None -> (
                 match dependent_affine_step_of_operand block older_chain rhs with
                 | Some (iv, coeff, bias) ->
                     Some
                       {
                         target = ReductionTempTarget temp;
                         subtract = false;
                         step = ReductionAffine { iv; coeff; bias };
                         carrier_temp = None;
                         alias_temps = [];
                       }
                 | None ->
                     let rhs =
                       match peel_self_delta block older_chain IntSet.empty rhs with
                       | Some peeled -> peeled
                       | None -> rhs
                     in
                     if debug_counted_local then
                       Printf.eprintf
                         "counted-carrier-fallback header=%s temp=%d side=lhs peeled=%s\n%!"
                         header temp (string_of_operand rhs);
                     Option.map
                       (fun (carrier_temp, step_expr, carrier_subtract, include_updated) ->
                         {
                           target = ReductionTempTarget temp;
                           subtract = false;
                           step =
                             ReductionCarrierProgression
                               {
                                 carrier_temp;
                                 step_expr;
                                 carrier_subtract;
                                 include_updated;
                               };
                           carrier_temp = None;
                           alias_temps = [];
                         })
                       (carrier_progression_of_operand block chain rhs)))
          else if resolves_to_self block older_chain IntSet.empty rhs then (
            if debug_counted_local then
              Printf.eprintf
                "counted-self-hit header=%s temp=%d side=rhs other=%s self={%s}\n%!"
                header temp
                (Printf.sprintf "%s/%s" (string_of_operand lhs) (debug_operand_def lhs))
                (string_of_temps self_temps);
            match
              reduction_step_of_operand
                invariant_loaded_places
                loop_defs
                def_blocks
                get_block
                loop_stable_phis
                multi_defs
                def_instrs
                ivs
                block lhs
            with
            | Some step ->
                Some
                  {
                    target = ReductionTempTarget temp;
                    subtract = false;
                    step;
                    carrier_temp = None;
                    alias_temps = [];
                  }
             | None -> (
                 match dependent_affine_step_of_operand block older_chain lhs with
                 | Some (iv, coeff, bias) ->
                     Some
                       {
                         target = ReductionTempTarget temp;
                         subtract = false;
                         step = ReductionAffine { iv; coeff; bias };
                         carrier_temp = None;
                         alias_temps = [];
                       }
                 | None ->
                     let lhs =
                       match peel_self_delta block older_chain IntSet.empty lhs with
                       | Some peeled -> peeled
                       | None -> lhs
                     in
                     if debug_counted_local then
                       Printf.eprintf
                         "counted-carrier-fallback header=%s temp=%d side=rhs peeled=%s\n%!"
                         header temp (string_of_operand lhs);
                     Option.map
                       (fun (carrier_temp, step_expr, carrier_subtract, include_updated) ->
                         {
                           target = ReductionTempTarget temp;
                           subtract = false;
                           step =
                             ReductionCarrierProgression
                               {
                                 carrier_temp;
                                 step_expr;
                                 carrier_subtract;
                                 include_updated;
                               };
                           carrier_temp = None;
                           alias_temps = [];
                         })
                       (carrier_progression_of_operand block chain lhs)))
          else None
      | Tcg.Bin (_, Sub, lhs, rhs) ->
          let lhs = resolve_on_update_chain block older_chain lhs in
          let rhs = resolve_on_update_chain block older_chain rhs in
          if resolves_to_self block older_chain IntSet.empty lhs then (
            if debug_counted_local then
              Printf.eprintf
                "counted-self-hit header=%s temp=%d side=sub-lhs other=%s self={%s}\n%!"
                header temp
                (Printf.sprintf "%s/%s" (string_of_operand rhs) (debug_operand_def rhs))
                (string_of_temps self_temps);
            match
              reduction_step_of_operand
                invariant_loaded_places
                loop_defs
                def_blocks
                get_block
                loop_stable_phis
                multi_defs
                def_instrs
                ivs
                block rhs
            with
            | Some step ->
                Some
                  {
                    target = ReductionTempTarget temp;
                    subtract = true;
                    step;
                    carrier_temp = None;
                    alias_temps = [];
                  }
             | None -> (
                 match dependent_affine_step_of_operand block older_chain rhs with
                 | Some (iv, coeff, bias) ->
                     Some
                       {
                         target = ReductionTempTarget temp;
                         subtract = true;
                         step = ReductionAffine { iv; coeff; bias };
                         carrier_temp = None;
                         alias_temps = [];
                       }
                 | None ->
                     let rhs =
                       match peel_self_delta block older_chain IntSet.empty rhs with
                       | Some peeled -> peeled
                       | None -> rhs
                     in
                     if debug_counted_local then
                       Printf.eprintf
                         "counted-carrier-fallback header=%s temp=%d side=sub peeled=%s\n%!"
                         header temp (string_of_operand rhs);
                     Option.map
                       (fun (carrier_temp, step_expr, carrier_subtract, include_updated) ->
                         {
                           target = ReductionTempTarget temp;
                           subtract = true;
                           step =
                             ReductionCarrierProgression
                               {
                                 carrier_temp;
                                 step_expr;
                                 carrier_subtract;
                                 include_updated;
                               };
                           carrier_temp = None;
                           alias_temps = [];
                         })
                       (carrier_progression_of_operand block chain rhs)))
          else None
      | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ | Tcg.Bin _ -> None
    in
    match last_def_of_temp_on_chain_with_block chain temp with
    | Some (block, Tcg.Move (_, src), older_chain) ->
        of_operand block older_chain IntSet.empty (resolve_on_update_chain block older_chain src)
    | Some (block, instr, older_chain) -> of_instr block older_chain IntSet.empty instr
    | None -> None
  in
  let reduction_update_of_place_on_chain place chain =
    match chain with
    | [] -> None
    | _ ->
        let block = flatten_chain_block chain in
        reduction_update_of_place
          invariant_loaded_places
          loop_defs
          def_blocks
          get_block
          loop_stable_phis
          multi_defs
          def_instrs
          ivs
          place
          block
  in
  let rec last_store_value_of_place_on_chain place chain =
    match chain with
    | [] -> None
    | (block : Cfg.block) :: rest -> (
        match last_store_of_place place block with
        | Some (_, value) -> Some (resolve_chain_operand chain value)
        | None -> last_store_value_of_place_on_chain place rest)
  in
  let place_alias_temp_on_chain place chain temp =
    match last_store_value_of_place_on_chain place chain with
    | Some stored_value ->
        resolve_chain_operand chain (Tcg.Temp temp) = stored_value
    | None -> false
  in
  if backedge_preds = [] then []
  else
      let temp_reductions =
        IntSet.fold
          (fun temp acc ->
            if IntSet.mem temp excluded_temps then acc
           else
             let common_self_temps =
               match backedge_preds with
               | [] -> IntSet.empty
               | pred :: rest ->
                   List.fold_left
                     (fun shared pred ->
                       IntSet.inter shared (self_temps_on_chain temp (update_chain_for_pred pred)))
                     (self_temps_on_chain temp (update_chain_for_pred pred))
                     rest
             in
             let has_outside_seed =
               IntSet.exists
                 (fun seed_temp ->
                   List.for_all
                     (fun pred ->
                       Option.is_some (last_def_of_temp_on_chain (phi_chain_for_pred pred) seed_temp))
                     outside_preds)
                 common_self_temps
             in
             if debug_counted_local then
               Printf.eprintf
                 "counted-temp-gate header=%s temp=%d seeds={%s} pass=%b\n%!"
                 header temp (string_of_temps common_self_temps) has_outside_seed;
             if has_outside_seed
             then
             let updates =
               List.filter_map
                 (fun pred -> reduction_update_of_temp_on_chain temp (update_chain_for_pred pred))
                 backedge_preds
             in
             if debug_counted_local then
               Printf.eprintf
                 "counted-temp-updates header=%s temp=%d count=%d preds=%d\n%!"
                 header temp (List.length updates) (List.length backedge_preds);
             match updates with
             | [] -> acc
             | first :: rest
               when List.length updates = List.length backedge_preds
                    && List.for_all (fun update -> update = first) rest ->
                 first :: acc
             | _ -> acc
             else acc)
         live_temps []
    in
    let place_reductions =
      PlaceSet.fold
        (fun place acc ->
          match place with
          | Tcg.Global _ -> acc
          | Tcg.Local _ ->
              let updates =
                List.filter_map
                  (fun pred -> reduction_update_of_place_on_chain place (update_chain_for_pred pred))
                  backedge_preds
              in
              match updates with
              | [] -> acc
              | first :: rest
                when List.length updates = List.length backedge_preds
                     && List.for_all (fun update -> update = first) rest ->
                  first :: acc
              | _ -> acc)
        live_places []
      |> List.map (fun reduction ->
             match reduction.target with
             | ReductionTempTarget _ -> reduction
             | ReductionPlaceTarget place ->
                 let alias_temps =
                   IntSet.elements live_temps
                   |> List.filter (fun temp -> not (IntSet.mem temp excluded_temps))
                   |> List.filter (fun temp ->
                          List.for_all
                            (fun pred -> place_alias_temp_on_chain place (update_chain_for_pred pred) temp)
                            backedge_preds)
                   |> List.sort_uniq compare
                 in
                 { reduction with alias_temps })
    in
    temp_reductions @ place_reductions

let collect_counted_place_mirrors
    header
    loop
    invariant_loaded_places
    loop_defs
    get_block
    def_blocks
    loop_stable_phis
    multi_defs
    def_instrs
    ivs
    live_places
    supported_temps
  =
  let header_block : Cfg.block = get_block header in
  let backedge_preds = List.filter (fun pred -> LabelSet.mem pred loop) header_block.preds in
  let update_chain_for_pred pred = incoming_update_chain get_block header pred in
  let canonical_temp_of_value block = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp when IntSet.mem temp supported_temps -> Some temp
    | Tcg.Temp temp ->
        let supported_alias =
          IntSet.elements supported_temps
          |> List.find_opt (fun target ->
                 target <> temp && resolves_to_temp multi_defs def_instrs target (Tcg.Temp temp))
        in
        match supported_alias with
        | Some target -> Some target
        | None ->
            List.find_map
          (fun (iv : basic_induction_var) ->
            if not (IntSet.mem iv.phi_temp supported_temps) then None
            else
              match
                reduction_update_of_temp
                  invariant_loaded_places
                  loop_defs
                  def_blocks
                  get_block
                  loop_stable_phis
                  multi_defs
                  def_instrs
                  ivs
                  iv.phi_temp
                  block
                  temp
              with
              | Some _ -> Some iv.phi_temp
              | None -> None)
          ivs
  in
  let last_store_value_of_place_on_chain place chain =
    let block = flatten_chain_block chain in
    match last_store_of_place place block with
    | Some (_, value) -> Some (resolve_chain_operand chain value, block)
    | None -> None
  in
  PlaceSet.elements live_places
  |> List.filter_map (fun place ->
         let mirrored_temps =
           List.filter_map
             (fun pred ->
               match last_store_value_of_place_on_chain place (update_chain_for_pred pred) with
               | Some (value, block) -> canonical_temp_of_value block value
               | None -> None)
             backedge_preds
         in
         match mirrored_temps with
          | [] -> None
          | first :: rest
            when List.length mirrored_temps = List.length backedge_preds
                 && List.for_all (( = ) first) rest
                 && IntSet.mem first supported_temps ->
              Some (place, first)
          | _ -> None)

let collect_reconstructible_live_temps
    invariant_loaded_places
    loop_defs
    get_block
    def_blocks
    loop_stable_phis
    multi_defs
    def_instrs
    supported_temps
    live_temps
  =
  let rec close supported order exprs =
    let newly_found_rev =
      IntSet.fold
        (fun temp acc ->
          if IntSet.mem temp supported || IntMap.mem temp exprs || IntSet.mem temp multi_defs then acc
          else
            match Hashtbl.find_opt def_blocks temp with
            | None -> acc
            | Some label -> (
                match
                  summary_expr_of_operand_with_bases
                    supported
                    invariant_loaded_places
                    loop_defs
                    def_blocks
                    get_block
                    loop_stable_phis
                    multi_defs
                    def_instrs
                    (get_block label)
                    (Tcg.Temp temp)
                with
                | Some expr -> (temp, expr) :: acc
                | None -> acc))
        live_temps []
    in
    match newly_found_rev with
    | [] -> (supported, List.rev order, exprs)
    | _ ->
        let supported, order, exprs =
          List.fold_left
            (fun (supported, order, exprs) (temp, expr) ->
              (IntSet.add temp supported, temp :: order, IntMap.add temp expr exprs))
            (supported, order, exprs) (List.rev newly_found_rev)
        in
        close supported order exprs
  in
  close supported_temps [] IntMap.empty

let build_triangle_number_instrs fresh_temp trip_temp =
  let n_minus_one = fresh_temp () in
  let half_n = fresh_temp () in
  let parity = fresh_temp () in
  let half_n_minus_one = fresh_temp () in
  let left = fresh_temp () in
  let right = fresh_temp () in
  let triangle = fresh_temp () in
  ( [ simplify_simple_instr (Tcg.Bin (n_minus_one, Sub, Tcg.Temp trip_temp, Tcg.Imm 1L));
      simplify_simple_instr (Tcg.Bin (half_n, Div, Tcg.Temp trip_temp, Tcg.Imm 2L));
      simplify_simple_instr (Tcg.Bin (parity, Mod, Tcg.Temp trip_temp, Tcg.Imm 2L));
      simplify_simple_instr (Tcg.Bin (half_n_minus_one, Div, Tcg.Temp n_minus_one, Tcg.Imm 2L));
      simplify_simple_instr (Tcg.Bin (left, Mul, Tcg.Temp half_n, Tcg.Temp n_minus_one));
      simplify_simple_instr (Tcg.Bin (right, Mul, Tcg.Temp parity, Tcg.Temp half_n_minus_one));
      simplify_simple_instr (Tcg.Bin (triangle, Add, Tcg.Temp left, Tcg.Temp right)) ],
    triangle )

let rec emit_summary_expr_with_carriers place_carriers fresh_temp = function
  | SummaryOperand operand -> ([], operand)
  | SummaryPlace place -> (
      match PlaceMap.find_opt place place_carriers with
      | Some temp -> ([], Tcg.Temp temp)
      | None ->
          let dst = fresh_temp () in
          ([ simplify_simple_instr (Tcg.Load (dst, place)) ], Tcg.Temp dst))
  | SummaryUn (op, expr) ->
      let instrs, operand = emit_summary_expr_with_carriers place_carriers fresh_temp expr in
      let dst = fresh_temp () in
      (instrs @ [ simplify_simple_instr (Tcg.Un (dst, op, operand)) ], Tcg.Temp dst)
  | SummaryBin (op, lhs, rhs) ->
      let lhs_instrs, lhs_operand =
        emit_summary_expr_with_carriers place_carriers fresh_temp lhs
      in
      let rhs_instrs, rhs_operand =
        emit_summary_expr_with_carriers place_carriers fresh_temp rhs
      in
      let dst = fresh_temp () in
      ( lhs_instrs @ rhs_instrs
        @ [ simplify_simple_instr (Tcg.Bin (dst, op, lhs_operand, rhs_operand)) ],
        Tcg.Temp dst )

let build_invariant_reduction_delta place_carriers fresh_temp trip_temp step_expr =
  let step_instrs, step_operand =
    emit_summary_expr_with_carriers place_carriers fresh_temp step_expr
  in
  match step_operand with
  | Tcg.Imm 0L -> (step_instrs, None)
  | Tcg.Imm 1L -> (step_instrs, Some (Tcg.Temp trip_temp))
  | Tcg.Imm -1L ->
      let delta = fresh_temp () in
      ( step_instrs
        @ [ simplify_simple_instr (Tcg.Bin (delta, Sub, Tcg.Imm 0L, Tcg.Temp trip_temp)) ],
        Some (Tcg.Temp delta) )
  | _ ->
      let delta = fresh_temp () in
      ( step_instrs
        @ [ simplify_simple_instr (Tcg.Bin (delta, Mul, Tcg.Temp trip_temp, step_operand)) ],
        Some (Tcg.Temp delta) )

let build_affine_reduction_delta
    place_carriers
    fresh_temp
    trip_temp
    (iv : basic_induction_var)
    coeff
    bias
  =
  let coeff_instrs, coeff_operand =
    emit_summary_expr_with_carriers place_carriers fresh_temp coeff
  in
  let bias_instrs, bias_operand =
    emit_summary_expr_with_carriers place_carriers fresh_temp bias
  in
  let scaled_base = fresh_temp () in
  let base_instrs =
    coeff_instrs
    @ [ simplify_simple_instr (Tcg.Bin (scaled_base, Mul, Tcg.Temp iv.phi_temp, coeff_operand)) ]
    @ bias_instrs
  in
  let base_operand, base_adjust_instrs =
    match bias_operand with
    | Tcg.Imm 0L -> (Tcg.Temp scaled_base, [])
    | _ ->
        let base = fresh_temp () in
        ( Tcg.Temp base,
          [ simplify_simple_instr (Tcg.Bin (base, Add, Tcg.Temp scaled_base, bias_operand)) ] )
  in
  let delta_base = fresh_temp () in
  let delta_instrs =
    [ simplify_simple_instr (Tcg.Bin (delta_base, Mul, base_operand, Tcg.Temp trip_temp)) ]
  in
  if iv.step = 0L then
    (base_instrs @ base_adjust_instrs @ delta_instrs, Some (Tcg.Temp delta_base))
  else
    let triangle_instrs, triangle = build_triangle_number_instrs fresh_temp trip_temp in
    let coeff_step_operand, coeff_step_instrs =
      if iv.step = 1L then (coeff_operand, [])
      else if iv.step = -1L then
        let coeff_step = fresh_temp () in
        ( Tcg.Temp coeff_step,
          [ simplify_simple_instr (Tcg.Bin (coeff_step, Sub, Tcg.Imm 0L, coeff_operand)) ] )
      else
        let coeff_step = fresh_temp () in
        ( Tcg.Temp coeff_step,
          [ simplify_simple_instr (Tcg.Bin (coeff_step, Mul, coeff_operand, Tcg.Imm iv.step)) ] )
    in
    let series = fresh_temp () in
    let series_instrs =
      coeff_step_instrs
      @ [ simplify_simple_instr (Tcg.Bin (series, Mul, coeff_step_operand, Tcg.Temp triangle)) ]
    in
    let delta = fresh_temp () in
    let combine = simplify_simple_instr (Tcg.Bin (delta, Add, Tcg.Temp delta_base, Tcg.Temp series)) in
    ( base_instrs @ base_adjust_instrs @ delta_instrs @ triangle_instrs @ series_instrs @ [ combine ],
      Some (Tcg.Temp delta) )

let build_carrier_progression_reduction_delta
    place_carriers
    fresh_temp
    trip_temp
    carrier_temp
    step_expr
    carrier_subtract
    include_updated
  =
  let base_delta = fresh_temp () in
  let base_instrs =
    [ simplify_simple_instr (Tcg.Bin (base_delta, Mul, Tcg.Temp carrier_temp, Tcg.Temp trip_temp)) ]
  in
  let step_instrs, step_operand =
    emit_summary_expr_with_carriers place_carriers fresh_temp step_expr
  in
  match step_operand with
  | Tcg.Imm 0L -> (base_instrs @ step_instrs, Some (Tcg.Temp base_delta))
  | _ ->
      let triangle_instrs, triangle = build_triangle_number_instrs fresh_temp trip_temp in
      let series_count, series_count_instrs =
        if include_updated then
          let series_count = fresh_temp () in
          ( Tcg.Temp series_count,
            [ simplify_simple_instr
                (Tcg.Bin (series_count, Add, Tcg.Temp triangle, Tcg.Temp trip_temp)) ] )
        else (Tcg.Temp triangle, [])
      in
      let signed_step, signed_step_instrs =
        if carrier_subtract then
          let negated = fresh_temp () in
          ( Tcg.Temp negated,
            [ simplify_simple_instr (Tcg.Bin (negated, Sub, Tcg.Imm 0L, step_operand)) ] )
        else (step_operand, [])
      in
      let series_delta = fresh_temp () in
      let total_delta = fresh_temp () in
      ( base_instrs
        @ step_instrs
        @ triangle_instrs
        @ series_count_instrs
        @ signed_step_instrs
        @ [ simplify_simple_instr (Tcg.Bin (series_delta, Mul, series_count, signed_step));
            simplify_simple_instr (Tcg.Bin (total_delta, Add, Tcg.Temp base_delta, Tcg.Temp series_delta)) ],
        Some (Tcg.Temp total_delta) )

let build_reduction_final_update fresh_temp trip_temp place_carriers (reduction : counted_reduction)
  =
  let delta_instrs, delta_operand =
    match reduction.step with
    | ReductionInvariant step_expr ->
        build_invariant_reduction_delta place_carriers fresh_temp trip_temp step_expr
    | ReductionAffine { iv; coeff; bias } ->
        build_affine_reduction_delta place_carriers fresh_temp trip_temp iv coeff bias
    | ReductionCarrierProgression
        { carrier_temp; step_expr; carrier_subtract; include_updated } ->
        build_carrier_progression_reduction_delta
          place_carriers
          fresh_temp
          trip_temp
          carrier_temp
          step_expr
          carrier_subtract
          include_updated
  in
  match delta_operand with
  | None -> []
  | Some delta_operand ->
      (match reduction.target with
      | ReductionTempTarget phi_temp ->
          let update =
            if reduction.subtract then
              simplify_simple_instr
                (Tcg.Bin
                   (phi_temp, Sub, Tcg.Temp phi_temp, delta_operand))
            else
              simplify_simple_instr
                (Tcg.Bin
                   (phi_temp, Add, Tcg.Temp phi_temp, delta_operand))
           in
          let alias_updates =
            List.map
              (fun temp -> simplify_simple_instr (Tcg.Move (temp, Tcg.Temp phi_temp)))
              reduction.alias_temps
          in
          delta_instrs @ [ update ] @ alias_updates
      | ReductionPlaceTarget place ->
          let acc_temp, acc_instrs =
            match reduction.carrier_temp with
            | Some temp -> (temp, [])
            | None ->
                let temp = fresh_temp () in
                (temp, [ simplify_simple_instr (Tcg.Load (temp, place)) ])
          in
          let update =
            if reduction.subtract then
              simplify_simple_instr
                (Tcg.Bin
                   (acc_temp, Sub, Tcg.Temp acc_temp, delta_operand))
            else
              simplify_simple_instr
                (Tcg.Bin
                   (acc_temp, Add, Tcg.Temp acc_temp, delta_operand))
           in
          let alias_updates =
            List.map
              (fun temp -> simplify_simple_instr (Tcg.Move (temp, Tcg.Temp acc_temp)))
              (List.filter (fun temp -> temp <> acc_temp) reduction.alias_temps)
          in
           acc_instrs
           @ delta_instrs
           @ [ update; Tcg.Store (place, Tcg.Temp acc_temp) ]
           @ alias_updates)

let build_live_temp_reconstruction_updates fresh_temp place_carriers reconstruction_order reconstruction_exprs
  =
  reconstruction_order
  |> List.concat_map (fun temp ->
         match IntMap.find_opt temp reconstruction_exprs with
         | None -> []
         | Some expr ->
             let instrs, operand =
               emit_summary_expr_with_carriers place_carriers fresh_temp expr
             in
             (match operand with
             | Tcg.Temp src when src = temp -> instrs
             | _ -> instrs @ [ simplify_simple_instr (Tcg.Move (temp, operand)) ]))

let loop_instr_count loop blocks =
  List.fold_left
    (fun acc (block : Cfg.block) ->
      if LabelSet.mem block.label loop then acc + List.length block.body else acc)
    0 blocks

let loop_memory_ops_count loop blocks =
  let instr_cost = function
    | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> 1
    | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ -> 0
  in
  List.fold_left
    (fun acc (block : Cfg.block) ->
      if LabelSet.mem block.label loop then
        acc + List.fold_left (fun sum instr -> sum + instr_cost instr) 0 block.body
      else acc)
    0 blocks

let instr_uses_temp temp = function
  | Tcg.Move (_, src)
  | Tcg.Un (_, _, src) ->
      operand_has_temp temp src
  | Tcg.Bin (_, _, lhs, rhs) -> operand_has_temp temp lhs || operand_has_temp temp rhs
  | Tcg.Load _ -> false
  | Tcg.Store (_, value) -> operand_has_temp temp value
  | Tcg.Call (_, _, args) -> List.exists (operand_has_temp temp) args

let term_uses_temp temp = function
  | Cfg.Jump _ | Cfg.Return None -> false
  | Cfg.BranchZero (cond, _, _)
  | Cfg.BranchNonZero (cond, _, _)
  | Cfg.Return (Some cond) ->
      operand_has_temp temp cond
  | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
      operand_has_temp temp lhs || operand_has_temp temp rhs

let collect_direct_extractable_reductions loop get_block backedge_preds reductions =
  let last_def_index_for_temp temp (block : Cfg.block) =
    let last_index = ref None in
    List.iteri
      (fun index instr ->
        match defs_temp instr with
        | Some dst when dst = temp -> last_index := Some index
        | Some _ | None -> ())
      block.body;
    !last_index
  in
  List.filter_map
    (fun (reduction : counted_reduction) ->
      match reduction.target with
      | ReductionPlaceTarget _ -> None
      | ReductionTempTarget phi_temp ->
          let allowed_defs =
            List.fold_left
              (fun acc pred ->
                match acc with
                | None -> None
                | Some acc -> (
                    match last_def_index_for_temp phi_temp (get_block pred) with
                    | Some index ->
                        let instr = List.nth (get_block pred).body index in
                        if instr_uses_temp phi_temp instr then Some ((pred, index) :: acc)
                        else None
                    | None -> None))
              (Some []) backedge_preds
          in
          match allowed_defs with
          | None -> None
          | Some allowed_defs ->
              let allowed_index label = List.assoc_opt label allowed_defs in
              let ok = ref true in
              LabelSet.iter
                (fun label ->
                  let block : Cfg.block = get_block label in
                  List.iteri
                    (fun index instr ->
                      if
                        instr_uses_temp phi_temp instr
                        || defs_temp instr = Some phi_temp
                      then
                        match allowed_index label with
                        | Some allowed when allowed = index -> ()
                        | Some _ | None -> ok := false)
                    block.body;
                  if term_uses_temp phi_temp block.term then ok := false)
                loop;
               if !ok then Some (reduction, allowed_defs) else None)
    reductions

let split_reductions_min_instrs = 12
let split_reductions_min_pressure = 2

let extract_counted_reductions_func summaries globals (f : Cfg.func) =
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let current_blocks = Hashtbl.create (List.length f.blocks + (2 * List.length headers)) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_block = get_block_exn current_blocks in
    let update_block (block : Cfg.block) =
      Hashtbl.replace current_blocks block.label block
    in
    let current_block_list () = Hashtbl.fold (fun _ block acc -> block :: acc) current_blocks [] in
    let next_temp = ref f.temp_count in
    let fresh_temp () =
      let temp = !next_temp in
      incr next_temp;
      temp
    in
    let new_blocks_rev = ref [] in
    let preheader_id = ref 0 in
    let fresh_preheader_label () =
      let id = !preheader_id in
      incr preheader_id;
      Printf.sprintf ".L%s_split_preheader_%d" f.label id
    in
    let summary_id = ref 0 in
    let fresh_summary_label () =
      let id = !summary_id in
      incr summary_id;
      Printf.sprintf ".L%s_split_summary_%d" f.label id
    in
    let changed = ref false in
    let current_entry = ref f.entry in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        let header_block : Cfg.block = get_block header in
        let blocks_snapshot = current_block_list () in
        let (loop_defs, def_blocks, def_instrs, multi_defs, loop_stable_phis, ivs, control) =
          analyze_counted_loop header loop get_block !next_temp blocks_snapshot
        in
        let effects = collect_loop_effects summaries globals loop blocks_snapshot in
        let invariant_loaded_places =
          PlaceSet.diff
            (local_places (locals_in_func { f with entry = !current_entry; blocks = blocks_snapshot }))
            (local_places effects.modified_places)
        in
        let total_instrs = loop_instr_count loop blocks_snapshot in
        let memory_ops = loop_memory_ops_count loop blocks_snapshot in
        match control with
        | None -> ()
        | Some info -> (
            match counted_loop_shape_supported info.control_label loop get_block info.inside_label with
            | false -> ()
            | true ->
                let live_in_t, live_in_p =
                  compute_liveness summaries globals
                    { f with entry = !current_entry; blocks = blocks_snapshot }
                in
                let live_t_exit = table_find_or_empty live_in_t info.exit_label IntSet.empty in
                let live_p_exit = table_find_or_empty live_in_p info.exit_label PlaceSet.empty in
                let live_ivs =
                  List.filter
                    (fun (iv : basic_induction_var) ->
                      iv.phi_temp = info.control_iv.phi_temp || IntSet.mem iv.phi_temp live_t_exit)
                    ivs
                in
                let loop_live_defs = IntSet.inter loop_defs live_t_exit in
                let excluded_temps =
                  List.fold_left
                    (fun acc (iv : basic_induction_var) -> IntSet.add iv.phi_temp acc)
                    IntSet.empty live_ivs
                in
                let reductions =
                  collect_counted_reductions
                    header
                    loop
                    invariant_loaded_places
                    loop_defs
                    get_block
                    def_blocks
                    loop_stable_phis
                    multi_defs
                    def_instrs
                    ivs
                    excluded_temps
                    loop_live_defs
                    (PlaceSet.inter (local_places effects.modified_places) live_p_exit)
                in
                let all_updates =
                  (List.map (fun iv -> CountedIv iv) live_ivs)
                  @ List.map (fun reduction -> CountedReduction reduction) reductions
                in
                let supported_live_temps =
                  List.fold_left
                    (fun acc update ->
                      match update with
                      | CountedIv _ ->
                          IntSet.add (counted_update_temp update) acc
                      | CountedReduction ({ target = ReductionTempTarget _; _ } as reduction) ->
                          add_reduction_alias_temps
                            (IntSet.add (counted_update_temp update) acc)
                            reduction
                      | CountedReduction ({ target = ReductionPlaceTarget _; _ } as reduction) ->
                          add_reduction_alias_temps acc reduction)
                    IntSet.empty all_updates
                in
                let supported_live_temps =
                  IntSet.fold
                    (fun temp acc ->
                      if operand_available_before_loop loop_defs multi_defs def_instrs (Tcg.Temp temp) then
                        IntSet.add temp acc
                      else acc)
                    loop_live_defs supported_live_temps
                in
                let supported_live_temps =
                  IntSet.union supported_live_temps (IntSet.inter loop_live_defs loop_stable_phis)
                in
                let supported_live_temps, _, _ =
                  collect_reconstructible_live_temps
                    invariant_loaded_places
                    loop_defs
                    get_block
                    def_blocks
                    loop_stable_phis
                    multi_defs
                    def_instrs
                    supported_live_temps
                    loop_live_defs
                in
                let place_mirrors =
                  collect_counted_place_mirrors
                    header
                    loop
                    invariant_loaded_places
                    loop_defs
                    get_block
                    def_blocks
                    loop_stable_phis
                    multi_defs
                    def_instrs
                    ivs
                    (PlaceSet.inter (local_places effects.modified_places) live_p_exit)
                    supported_live_temps
                in
                let supported_live_places =
                  List.fold_left
                    (fun acc update ->
                      match counted_update_place update with
                      | Some place -> PlaceSet.add place acc
                      | None -> acc)
                    PlaceSet.empty all_updates
                  |> fun acc ->
                  List.fold_left (fun acc (place, _) -> PlaceSet.add place acc) acc place_mirrors
                in
                let loop_live_places =
                  PlaceSet.inter (local_places effects.modified_places) live_p_exit
                in
                if
                  IntSet.subset loop_live_defs supported_live_temps
                  && PlaceSet.subset loop_live_places supported_live_places
                then ()
                else
                  let extractable =
                    collect_direct_extractable_reductions
                    loop
                    get_block
                    info.control_iv.backedge_preds
                    reductions
                  in
                  let pressure_relief =
                    PlaceSet.cardinal loop_live_places
                    + IntSet.cardinal (IntSet.diff loop_live_defs supported_live_temps)
                    + List.length extractable
                  in
                  if extractable = [] then ()
                  else if total_instrs < split_reductions_min_instrs then ()
                  else if pressure_relief < split_reductions_min_pressure then ()
                  else if memory_ops = 0 && pressure_relief < 3 then ()
                  else
                    let outside_preds =
                      List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
                    in
                    if outside_preds = [] && header <> !current_entry then ()
                    else
                      let removals = Hashtbl.create 8 in
                      List.iter
                        (fun (_, defs) ->
                          List.iter
                            (fun (label, index) ->
                              let current =
                                match Hashtbl.find_opt removals label with
                                | Some set -> set
                                | None -> IntSet.empty
                              in
                              Hashtbl.replace removals label (IntSet.add index current))
                            defs)
                        extractable;
                      let preheader_label =
                        match outside_preds with
                        | [ pred ] ->
                            let pred_block = get_block pred in
                            if pred_block.succs = [ header ] then pred else fresh_preheader_label ()
                        | [] -> fresh_preheader_label ()
                        | _ -> fresh_preheader_label ()
                      in
                      let created_preheader = not (Hashtbl.mem current_blocks preheader_label) in
                      if created_preheader then begin
                        let redirects = Hashtbl.create (List.length outside_preds) in
                        List.iter
                          (fun pred -> Hashtbl.add redirects (pred, header) preheader_label)
                          outside_preds;
                        List.iter
                          (fun pred ->
                            let pred_block = get_block pred in
                            let term = redirect_successors pred redirects pred_block.term in
                            update_block { pred_block with term; succs = Cfg.successors term })
                          outside_preds;
                        Hashtbl.add current_blocks preheader_label
                          {
                            Cfg.label = preheader_label;
                            body = [];
                            term = Cfg.Jump header;
                            preds = [];
                            succs = [ header ];
                          };
                        new_blocks_rev := preheader_label :: !new_blocks_rev;
                        if header = !current_entry then current_entry := preheader_label
                      end;
                      let trip_instrs, trip_temp =
                        build_trip_count_instrs
                          fresh_temp
                          info.control_iv.phi_temp
                          info.control_iv.step
                          info.kind
                      in
                      let extracted_reductions =
                        extractable |> List.map fst
                        |> materialize_place_reduction_carriers fresh_temp
                      in
                      let extracted_reductions, carrier_preloads = extracted_reductions in
                      let place_carriers = place_carriers_of_reductions extracted_reductions in
                      let preheader = get_block preheader_label in
                      update_block
                        {
                          preheader with
                          body = preheader.body @ trip_instrs @ carrier_preloads;
                        };
                      Hashtbl.iter
                        (fun label indexes ->
                          let block : Cfg.block = get_block label in
                          let body =
                            block.body
                            |> List.mapi (fun index instr -> (index, instr))
                            |> List.filter (fun (index, _) -> not (IntSet.mem index indexes))
                            |> List.map snd
                          in
                          update_block { block with body })
                        removals;
                      let summary_label = fresh_summary_label () in
                      let summary_body =
                        extracted_reductions
                        |> List.concat_map
                             (build_reduction_final_update fresh_temp trip_temp place_carriers)
                      in
                      let control_block = get_block info.control_label in
                      let term =
                        rewrite_term_successor control_block.term
                          ~from_label:info.exit_label ~to_label:summary_label
                      in
                      update_block { control_block with term; succs = Cfg.successors term };
                      Hashtbl.add current_blocks summary_label
                        {
                          Cfg.label = summary_label;
                          body = summary_body;
                          term = Cfg.Jump info.exit_label;
                          preds = [];
                          succs = [ info.exit_label ];
                        };
                      new_blocks_rev := summary_label :: !new_blocks_rev;
                      changed := true))
      headers;
    if !changed then
      let ordered_labels = List.map (fun (block : Cfg.block) -> block.label) f.blocks in
      let blocks = List.map get_block ordered_labels @ List.rev_map get_block !new_blocks_rev in
      Cfg.rebuild_edges { f with entry = !current_entry; temp_count = !next_temp; blocks }
    else f

let eliminate_counted_loops_func summaries globals (f : Cfg.func) =
  let debug_counted = Sys.getenv_opt "TOYC_DEBUG_COUNTED_LOOPS" <> None in
  let debugf fmt = Printf.ksprintf (fun s -> if debug_counted then prerr_endline s) fmt in
  let term_kind = function
    | Cfg.Jump _ -> "jump"
    | Cfg.BranchZero _ -> "branch_zero"
    | Cfg.BranchNonZero _ -> "branch_nonzero"
    | Cfg.BranchCompare _ -> "branch_compare"
    | Cfg.Return _ -> "return"
  in
  let instr_kind = function
    | Tcg.Move _ -> "move"
    | Tcg.Un _ -> "un"
    | Tcg.Bin _ -> "bin"
    | Tcg.Load _ -> "load"
    | Tcg.Store _ -> "store"
    | Tcg.Call _ -> "call"
  in
  let string_of_intset set =
    IntSet.elements set |> List.map string_of_int |> String.concat ","
  in
  let string_of_ivs ivs =
    ivs
    |> List.map (fun (iv : basic_induction_var) -> Printf.sprintf "%d:%Ld" iv.phi_temp iv.step)
    |> String.concat ";"
  in
  let string_of_place = function
    | Tcg.Local id -> Printf.sprintf "local:%d" id
    | Tcg.Global label -> Printf.sprintf "global:%s" label
  in
  let string_of_places set =
    PlaceSet.elements set |> List.map string_of_place |> String.concat ","
  in
  let string_of_place_mirrors mirrors =
    mirrors
    |> List.map (fun (place, temp) -> Printf.sprintf "%s->%d" (string_of_place place) temp)
    |> String.concat ","
  in
  let string_of_operand = function
    | Tcg.Imm value -> Int64.to_string value
    | Tcg.Temp temp -> Printf.sprintf "t%d" temp
  in
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let current_blocks = Hashtbl.create (List.length f.blocks + List.length headers) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_block = get_block_exn current_blocks in
    let update_block (block : Cfg.block) =
      Hashtbl.replace current_blocks block.label block
    in
    let current_block_list () = Hashtbl.fold (fun _ block acc -> block :: acc) current_blocks [] in
    let next_temp = ref f.temp_count in
    let fresh_temp () =
      let temp = !next_temp in
      incr next_temp;
      temp
    in
    let summary_id = ref 0 in
    let fresh_summary_label () =
      let id = !summary_id in
      incr summary_id;
      Printf.sprintf ".L%s_counted_loop_%d" f.label id
    in
    let new_blocks_rev = ref [] in
    let changed = ref false in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        let header_block : Cfg.block = get_block header in
        let blocks_snapshot = current_block_list () in
        let (loop_defs, def_blocks, def_instrs, multi_defs, loop_stable_phis, ivs, control) =
          analyze_counted_loop header loop get_block !next_temp blocks_snapshot
        in
        let effects = collect_loop_effects summaries globals loop blocks_snapshot in
        let invariant_loaded_places =
          PlaceSet.diff
            (local_places (locals_in_func { f with blocks = blocks_snapshot }))
            (local_places effects.modified_places)
        in
        match control with
        | None ->
            debugf "counted-skip func=%s header=%s reason=classify term=%s ivs=%d preds=%d"
              f.name header (term_kind header_block.term) (List.length ivs)
              (List.length header_block.preds)
        | Some info -> (
            match counted_loop_shape_supported info.control_label loop get_block info.inside_label with
            | false ->
                debugf "counted-skip func=%s header=%s reason=nonlinear_path" f.name header
            | true ->
                let live_in_t, live_in_p =
                  compute_liveness summaries globals { f with blocks = blocks_snapshot }
                in
                let live_p_exit = table_find_or_empty live_in_p info.exit_label PlaceSet.empty in
                let modified_globals = global_places effects.modified_places in
                let loop_live_places =
                  PlaceSet.inter (local_places effects.modified_places) live_p_exit
                in
                let live_t_exit = table_find_or_empty live_in_t info.exit_label IntSet.empty in
                let live_ivs =
                  List.filter
                    (fun (iv : basic_induction_var) ->
                      iv.phi_temp = info.control_iv.phi_temp || IntSet.mem iv.phi_temp live_t_exit)
                    ivs
                in
                let loop_live_defs =
                  IntSet.inter loop_defs live_t_exit
                in
                let excluded_temps =
                  List.fold_left
                    (fun acc (iv : basic_induction_var) -> IntSet.add iv.phi_temp acc)
                    IntSet.empty live_ivs
                in
                let reductions =
                  collect_counted_reductions
                    header
                    loop
                    invariant_loaded_places
                    loop_defs
                    get_block
                    def_blocks
                    loop_stable_phis
                    multi_defs
                    def_instrs
                    ivs
                    excluded_temps
                    loop_live_defs
                    loop_live_places
                in
                let all_updates =
                  (List.map (fun iv -> CountedIv iv) live_ivs)
                  @ List.map (fun reduction -> CountedReduction reduction) reductions
                in
                let supported_live_temps =
                  List.fold_left
                    (fun acc update ->
                      match update with
                      | CountedIv _ ->
                          IntSet.add (counted_update_temp update) acc
                      | CountedReduction ({ target = ReductionTempTarget _; _ } as reduction) ->
                          add_reduction_alias_temps
                            (IntSet.add (counted_update_temp update) acc)
                            reduction
                      | CountedReduction ({ target = ReductionPlaceTarget _; _ } as reduction) ->
                          add_reduction_alias_temps acc reduction)
                    IntSet.empty all_updates
                in
                let supported_live_temps =
                  IntSet.fold
                    (fun temp acc ->
                      if operand_available_before_loop loop_defs multi_defs def_instrs (Tcg.Temp temp) then
                        IntSet.add temp acc
                      else acc)
                    loop_live_defs supported_live_temps
                in
                let supported_live_temps =
                  IntSet.union supported_live_temps (IntSet.inter loop_live_defs loop_stable_phis)
                in
                let supported_live_temps, reconstruction_order, reconstruction_exprs =
                  collect_reconstructible_live_temps
                    invariant_loaded_places
                    loop_defs
                    get_block
                    def_blocks
                    loop_stable_phis
                    multi_defs
                    def_instrs
                    supported_live_temps
                    loop_live_defs
                in
                let place_mirrors =
                  collect_counted_place_mirrors
                    header
                    loop
                    invariant_loaded_places
                    loop_defs
                    get_block
                    def_blocks
                    loop_stable_phis
                    multi_defs
                    def_instrs
                    ivs
                    loop_live_places
                    supported_live_temps
                in
                if debug_counted then
                  let backedge_preds =
                    List.filter (fun pred -> LabelSet.mem pred loop) header_block.preds
                  in
                  let last_store_value_of_place_on_chain place chain =
                    let block = flatten_chain_block chain in
                    match last_store_of_place place block with
                    | Some (_, value) -> Some (resolve_chain_operand chain value)
                    | None -> None
                  in
                  PlaceSet.iter
                    (fun place ->
                      let stores =
                        backedge_preds
                        |> List.map (fun pred ->
                               let chain = incoming_update_chain get_block header pred in
                               let value =
                                 match last_store_value_of_place_on_chain place chain with
                                 | Some operand -> (
                                     match operand with
                                     | Tcg.Imm _ -> string_of_operand operand
                                     | Tcg.Temp temp ->
                                         let def_label =
                                           Option.value ~default:"<none>"
                                             (Hashtbl.find_opt def_blocks temp)
                                         in
                                         let def_kind =
                                           match Hashtbl.find_opt def_instrs temp with
                                           | Some instr -> instr_kind instr
                                           | None -> "none"
                                         in
                                         Printf.sprintf "%s@%s/%s" (string_of_operand operand)
                                           def_label def_kind)
                                 | None -> "<none>"
                               in
                               Printf.sprintf "%s:%s" pred value)
                        |> String.concat ";"
                      in
                      debugf "counted-place-detail func=%s header=%s place=%s stores=[%s]"
                        f.name header (string_of_place place) stores)
                    loop_live_places;
                let supported_live_places =
                  List.fold_left
                    (fun acc update ->
                      match counted_update_place update with
                      | Some place -> PlaceSet.add place acc
                      | None -> acc)
                    PlaceSet.empty all_updates
                  |> fun acc ->
                  List.fold_left (fun acc (place, _) -> PlaceSet.add place acc) acc place_mirrors
                in
                debugf
                  "counted-candidate func=%s header=%s exit=%s ivs=[%s] live_defs={%s} live_places={%s} reductions=%d supported={%s} mirrors={%s}"
                  f.name header info.exit_label (string_of_ivs ivs)
                  (string_of_intset loop_live_defs)
                  (string_of_places loop_live_places)
                  (List.length reductions)
                  (string_of_intset supported_live_temps)
                  (string_of_place_mirrors place_mirrors);
                if effects.has_call || not (PlaceSet.is_empty modified_globals) then
                  debugf "counted-skip func=%s header=%s reason=effects" f.name header
                else if not (IntSet.subset loop_live_defs supported_live_temps) then
                  let missing = IntSet.diff loop_live_defs supported_live_temps in
                  debugf "counted-skip func=%s header=%s reason=unsupported_live missing={%s}"
                    f.name header
                    (string_of_intset missing);
                  IntSet.iter
                    (fun temp ->
                      let def_label =
                        match Hashtbl.find_opt def_blocks temp with
                        | Some label -> label
                        | None -> "<none>"
                      in
                      let def_kind =
                        match Hashtbl.find_opt def_instrs temp with
                        | Some instr -> instr_kind instr
                        | None -> "none"
                      in
                      debugf
                        "counted-missing-temp func=%s header=%s temp=%d def_block=%s def_kind=%s"
                        f.name header temp def_label def_kind)
                    missing
                else if not (PlaceSet.subset loop_live_places supported_live_places) then
                  debugf
                    "counted-skip func=%s header=%s reason=unsupported_live_places missing={%s} supported_places={%s}"
                    f.name header
                    (string_of_places (PlaceSet.diff loop_live_places supported_live_places))
                    (string_of_places supported_live_places)
                else
                  let reductions, carrier_preloads =
                    materialize_place_reduction_carriers fresh_temp reductions
                  in
                  let place_carriers = place_carriers_of_reductions reductions in
                  let trip_instrs, trip_temp =
                    build_trip_count_instrs
                      fresh_temp
                      info.control_iv.phi_temp
                      info.control_iv.step
                      info.kind
                  in
                  let updates =
                    carrier_preloads
                    @ List.concat_map
                        (build_reduction_final_update fresh_temp trip_temp place_carriers)
                        reductions
                    @ List.concat_map
                        (build_iv_final_update fresh_temp trip_temp)
                        live_ivs
                    @ build_live_temp_reconstruction_updates
                        fresh_temp
                        place_carriers
                        reconstruction_order
                        reconstruction_exprs
                    @ List.map
                        (fun (place, temp) -> Tcg.Store (place, Tcg.Temp temp))
                        place_mirrors
                  in
                  let summary_label = fresh_summary_label () in
                  let control_block = get_block info.control_label in
                  let term =
                    rewrite_term_successor control_block.term
                      ~from_label:info.inside_label ~to_label:summary_label
                  in
                  update_block { control_block with term; succs = Cfg.successors term };
                  Hashtbl.add current_blocks summary_label
                    {
                      Cfg.label = summary_label;
                      body = trip_instrs @ updates;
                      term = Cfg.Jump info.exit_label;
                      preds = [];
                      succs = [ info.exit_label ];
                    };
                  debugf "counted-apply func=%s header=%s summary=%s updates=%d" f.name header
                    summary_label (List.length all_updates);
                  new_blocks_rev := summary_label :: !new_blocks_rev;
                  changed := true))
      headers;
    if !changed then
      let ordered_labels = List.map (fun (block : Cfg.block) -> block.label) f.blocks in
      let blocks = List.map get_block ordered_labels @ List.rev_map get_block !new_blocks_rev in
      Cfg.rebuild_edges { f with temp_count = !next_temp; blocks }
    else f

let full_unroll_counted_loops_func summaries globals (f : Cfg.func) =
  let full_unroll_max_trip = 8L in
  let full_unroll_max_blocks = 4 in
  let full_unroll_max_instrs = 28 in
  let full_unroll_max_control_body_instrs = 4 in
  let control_body_supported body =
    List.length body <= full_unroll_max_control_body_instrs
    && List.for_all pure_cfg_prep_instr body
  in
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let current_blocks = Hashtbl.create (List.length f.blocks + (8 * List.length headers)) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let block_order = ref (List.map (fun (block : Cfg.block) -> block.label) f.blocks) in
    let get_block = get_block_exn current_blocks in
    let current_block_list () = List.map get_block !block_order in
    let insert_after label new_labels =
      block_order :=
        List.concat_map
          (fun current -> if current = label then current :: new_labels else [ current ])
          !block_order
    in
    let next_id = ref 0 in
    let fresh_unroll_label iter index =
      let id = !next_id in
      Printf.sprintf ".L%s_full_unroll_%d_%d_%d" f.label id iter index
    in
    let changed = ref false in
    let current_entry = ref f.entry in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        let blocks_snapshot = current_block_list () in
        let (loop_defs, _, def_instrs, multi_defs, _, _, control) =
          analyze_counted_loop header loop get_block f.temp_count blocks_snapshot
        in
        let effects = collect_loop_effects summaries globals loop blocks_snapshot in
        match control with
        | None -> ()
        | Some info -> (
            let control_block : Cfg.block = get_block info.control_label in
            match linear_loop_path info.control_label loop get_block info.inside_label with
            | None -> ()
            | Some path ->
                let outside_preds =
                  let header_block : Cfg.block = get_block header in
                  List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
                in
                let total_instrs =
                  List.length control_block.body
                  + List.fold_left
                      (fun acc (block : Cfg.block) -> acc + List.length block.body)
                      0 path
                in
                let modified_globals = global_places effects.modified_places in
                let resolve_const operand =
                  match resolve_operand_before_loop loop_defs multi_defs def_instrs operand with
                  | Some (Tcg.Imm value) -> Some value
                  | Some (Tcg.Temp _) | None -> None
                in
                let init_values =
                  info.control_iv.outside_inputs
                  |> List.filter_map (fun (_, operand) -> resolve_const operand)
                  |> List.sort_uniq compare
                in
                let trip_count =
                  match init_values with
                  | [ init_value ] ->
                      constant_trip_count_of_kind resolve_const init_value info.control_iv.step info.kind
                  | _ -> None
                in
                if
                  effects.has_call
                  || not (PlaceSet.is_empty modified_globals)
                  || not (control_body_supported control_block.body)
                  || path = []
                  || List.length path > full_unroll_max_blocks
                  || total_instrs > full_unroll_max_instrs
                  || (outside_preds = [] && header <> !current_entry)
                then ()
                else
                  match trip_count with
                  | Some trip when 0L <= trip && trip <= full_unroll_max_trip ->
                      let target_label =
                        if trip = 0L then info.exit_label
                        else
                          let trip_int = Int64.to_int trip in
                          let copies =
                            Array.init trip_int (fun iter ->
                                Array.of_list
                                  (List.mapi
                                     (fun index (block : Cfg.block) ->
                                       (block.label, fresh_unroll_label iter index))
                                     path))
                          in
                          incr next_id;
                          let rename copied_labels label =
                            Array.fold_left
                              (fun acc (original, renamed) ->
                                match acc with Some _ -> acc | None -> if original = label then Some renamed else None)
                              None copied_labels
                            |> Option.value ~default:label
                          in
                          let next_entry iter =
                            if iter + 1 < trip_int then snd copies.(iter + 1).(0) else info.exit_label
                          in
                          let new_labels = ref [] in
                          Array.iteri
                            (fun iter copied_labels ->
                              let copied_blocks =
                                List.mapi
                                  (fun index (block : Cfg.block) ->
                                    let label = snd copied_labels.(index) in
                                    let term =
                                      if index + 1 = List.length path then
                                        Cfg.Jump (next_entry iter)
                                      else rewrite_term_labels (rename copied_labels) block.term
                                    in
                                    let body =
                                      if index + 1 = List.length path then block.body @ control_block.body
                                      else block.body
                                    in
                                    { block with label; body; term; succs = Cfg.successors term })
                                  path
                              in
                              List.iter
                                (fun (block : Cfg.block) ->
                                  Hashtbl.add current_blocks block.label block;
                                  new_labels := block.label :: !new_labels)
                                copied_blocks)
                            copies;
                          let entry_label = snd copies.(0).(0) in
                          insert_after info.control_label (List.rev !new_labels);
                          changed := true;
                          entry_label
                      in
                      List.iter
                        (fun pred ->
                          let pred_block = get_block pred in
                          let term =
                            rewrite_term_successor pred_block.term ~from_label:header ~to_label:target_label
                          in
                          Hashtbl.replace current_blocks pred
                            { pred_block with term; succs = Cfg.successors term })
                        outside_preds;
                      if header = !current_entry then current_entry := target_label
                  | Some _ | None -> ()))
      headers;
    if !changed then
      let blocks = List.map get_block !block_order in
      Cfg.rebuild_edges { f with entry = !current_entry; blocks }
    else f

let unroll_counted_loops_x2_func summaries globals (f : Cfg.func) =
  let debug_unroll_pair = Sys.getenv_opt "TOYC_DEBUG_UNROLL_PAIR" <> None in
  let unroll_single_path_max_blocks = 6 in
  let unroll_linear_path_max_blocks = 4 in
  let unroll_single_block_min_instrs = 4 in
  let unroll_multi_block_min_instrs = 6 in
  let unroll_single_block_max_instrs = 32 in
  let unroll_small_path_max_instrs = 24 in
  let unroll_large_path_max_instrs = 20 in
  let unroll_single_block_max_memory_ops = 8 in
  let unroll_small_path_max_memory_ops = 5 in
  let unroll_large_path_max_memory_ops = 4 in
  let unroll_single_block_max_defs = 12 in
  let unroll_multi_block_max_defs = 8 in
  let unroll_max_control_body_instrs = 4 in
  let control_body_supported body =
    List.length body <= unroll_max_control_body_instrs
    && List.for_all pure_cfg_prep_instr body
  in
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let current_blocks = Hashtbl.create (List.length f.blocks + (2 * List.length headers)) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let block_order = ref (List.map (fun (block : Cfg.block) -> block.label) f.blocks) in
    let get_block = get_block_exn current_blocks in
    let update_block (block : Cfg.block) =
      Hashtbl.replace current_blocks block.label block
    in
    let current_block_list () = List.map get_block !block_order in
    let insert_after label new_labels =
      block_order :=
        List.concat_map
          (fun current -> if current = label then current :: new_labels else [ current ])
          !block_order
    in
    let unroll_id = ref 0 in
    let fresh_unroll_label index =
      let id = !unroll_id in
      Printf.sprintf ".L%s_unroll2_%d_%d" f.label id index
    in
    let changed = ref false in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        if is_unroll2_label header || LabelSet.exists is_unroll2_label loop then ()
        else
          let blocks_snapshot = current_block_list () in
          let (loop_defs, _, def_instrs, multi_defs, _, _, control) =
            analyze_counted_loop header loop get_block f.temp_count blocks_snapshot
          in
          let effects = collect_loop_effects summaries globals loop blocks_snapshot in
          match control with
          | None -> ()
          | Some info -> (
              let control_block : Cfg.block = get_block info.control_label in
              match linear_loop_path info.control_label loop get_block info.inside_label with
              | None -> ()
              | Some path ->
                  let path_blocks = List.length path in
                  let one_block_path = path_blocks <= 1 in
                  let path_max_blocks =
                    if one_block_path then unroll_single_path_max_blocks else unroll_linear_path_max_blocks
                  in
                  let min_instrs =
                    if one_block_path then unroll_single_block_min_instrs else unroll_multi_block_min_instrs
                  in
                  let max_instrs =
                    if one_block_path then unroll_single_block_max_instrs
                    else if path_blocks <= 2 then unroll_small_path_max_instrs
                    else unroll_large_path_max_instrs
                  in
                  let max_memory_ops =
                    if one_block_path then unroll_single_block_max_memory_ops
                    else if path_blocks <= 2 then unroll_small_path_max_memory_ops
                    else unroll_large_path_max_memory_ops
                  in
                  let has_redefined_candidate_temp =
                    let counts = Hashtbl.create 16 in
                    let note_instr instr =
                      match defs_temp instr with
                      | Some temp ->
                          let count = Option.value ~default:0 (Hashtbl.find_opt counts temp) in
                          Hashtbl.replace counts temp (count + 1)
                      | None -> ()
                    in
                    List.iter note_instr control_block.body;
                     List.iter
                       (fun (block : Cfg.block) -> List.iter note_instr block.body)
                       path;
                     Hashtbl.fold (fun _ count seen -> seen || count > 1) counts false
                   in
                  let total_instrs =
                    List.length control_block.body
                    + List.fold_left
                        (fun acc (block : Cfg.block) -> acc + List.length block.body)
                        0 path
                  in
                  let memory_ops =
                    List.fold_left
                      (fun acc (block : Cfg.block) ->
                        acc
                        + List.fold_left
                            (fun sum instr ->
                              sum
                              +
                              match instr with
                              | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> 1
                              | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ -> 0)
                            0 block.body)
                      0 path
                  in
                  let unique_defs =
                    let defs = Hashtbl.create 16 in
                    let note_instr instr =
                      match defs_temp instr with
                      | Some temp -> Hashtbl.replace defs temp ()
                      | None -> ()
                    in
                    List.iter note_instr control_block.body;
                    List.iter (fun (block : Cfg.block) -> List.iter note_instr block.body) path;
                    Hashtbl.length defs
                  in
                  (* A constant even trip count lets the x2 unroll execute the two
                     bodies as an inseparable pair.  The guard between the first
                     and second copies can then never exit.  Only use this fast
                     path when the pure control-preparation temps are private to
                     the guard; otherwise skipping that preparation could change
                     a value observed elsewhere. *)
                  let control_body_defs_are_guard_private =
                    let defs =
                      List.fold_left
                        (fun acc instr ->
                          match defs_temp instr with
                          | Some temp -> IntSet.add temp acc
                          | None -> acc)
                        IntSet.empty control_block.body
                    in
                    IntSet.for_all
                      (fun temp ->
                        List.for_all
                          (fun (block : Cfg.block) ->
                            if block.label = info.control_label then true
                            else
                              not
                                (List.exists (instr_uses_temp temp) block.body
                                || term_uses_temp temp block.term))
                          blocks_snapshot)
                      defs
                  in
                  let exact_trip_count =
                    let resolve_const operand =
                      match resolve_operand_before_loop loop_defs multi_defs def_instrs operand with
                      | Some (Tcg.Imm value) -> Some value
                      | Some (Tcg.Temp _) | None -> None
                    in
                    let init_values =
                      info.control_iv.outside_inputs
                      |> List.filter_map (fun (_, operand) -> resolve_const operand)
                      |> List.sort_uniq compare
                    in
                    match init_values with
                    | [ init_value ] ->
                        constant_trip_count_of_kind
                          resolve_const init_value info.control_iv.step info.kind
                    | _ -> None
                  in
                  let control_body_nontrapping =
                    List.for_all
                      (function
                        | Tcg.Bin (_, (Div | Mod), _, _) -> false
                        | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ -> true
                        | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> false)
                      control_block.body
                  in
                  let can_pair_without_mid_guard =
                    control_body_defs_are_guard_private
                    && control_body_nontrapping
                    &&
                    match exact_trip_count with
                    | Some trip -> trip >= 2L && Int64.rem trip 2L = 0L
                    | None -> false
                  in
                  let enough_benefit =
                    total_instrs >= min_instrs
                    && (memory_ops >= 2 || total_instrs >= (if one_block_path then 8 else 10))
                  in
                  if
                    effects.has_call
                    || not (control_body_supported control_block.body)
                    || path = []
                    || path_blocks > path_max_blocks
                    || total_instrs > max_instrs
                    || memory_ops > max_memory_ops
                    || unique_defs > (if one_block_path then unroll_single_block_max_defs else unroll_multi_block_max_defs)
                    || (PlaceSet.is_empty effects.modified_places && not enough_benefit)
                    || has_redefined_candidate_temp
                  then ()
                  else
                    let last_block = List.hd (List.rev path) in
                    if last_block.succs <> [ info.control_label ] then ()
                    else
                      let copied_labels =
                        List.mapi (fun index (block : Cfg.block) -> (block.label, fresh_unroll_label index)) path
                      in
                      incr unroll_id;
                      let rename label =
                        match List.assoc_opt label copied_labels with
                        | Some renamed -> renamed
                        | None -> label
                      in
                      let copied_blocks =
                        List.map
                          (fun (block : Cfg.block) ->
                            let label = rename block.label in
                            let term = rewrite_term_labels rename block.term in
                            { block with label; term; succs = Cfg.successors term })
                          path
                      in
                      let copied_entry =
                        match copied_blocks with
                        | first :: _ -> first.label
                        | [] -> failwith "internal empty unroll path"
                      in
                      if can_pair_without_mid_guard && debug_unroll_pair then
                        Printf.eprintf
                          "unroll2-pair func=%s header=%s trip=%s\n%!"
                          f.name header
                          (match exact_trip_count with
                          | Some trip -> Int64.to_string trip
                          | None -> "?");
                      let body, term =
                        if can_pair_without_mid_guard then
                          (last_block.body, Cfg.Jump copied_entry)
                        else
                          let term =
                            rewrite_term_successor control_block.term
                              ~from_label:info.inside_label ~to_label:copied_entry
                          in
                          (last_block.body @ control_block.body, term)
                      in
                      update_block
                        {
                          last_block with
                          body;
                          term;
                          succs = Cfg.successors term;
                        };
                      List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) copied_blocks;
                      insert_after last_block.label (List.map (fun (block : Cfg.block) -> block.label) copied_blocks);
                      changed := true))
      headers;
    if !changed then
      let blocks = List.map get_block !block_order in
      Cfg.rebuild_edges { f with blocks }
    else f

(* Final-only loop-bound materialization.  BranchCompare has no immediate
   RISC-V form, so codegen otherwise emits a fresh [li] every dynamic trip
   through the branch.  For small, call-free loops that came from our x2
   counted-loop unroller, keep one invariant bound temp in the existing direct
   preheader instead.  This pass deliberately runs after all iterative
   middle-end passes so constant propagation cannot fold the temp back into an
   immediate. *)
let hoist_unrolled_loop_branch_immediates_func summaries globals (f : Cfg.func) =
  let debug_bound_hoist = Sys.getenv_opt "TOYC_DEBUG_LOOP_BOUND_HOIST" <> None in
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let current_blocks = Hashtbl.create (List.length f.blocks) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_block = get_block_exn current_blocks in
    let update_block (block : Cfg.block) = Hashtbl.replace current_blocks block.label block in
    let next_temp = ref f.temp_count in
    let fresh_temp () =
      let temp = !next_temp in
      incr next_temp;
      temp
    in
    let changed = ref false in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        (* Restrict this to loops already selected by the profitable x2 unroller.
           That keeps the extra long-lived register away from unrelated loops. *)
        if not (LabelSet.exists is_unroll2_label loop) then ()
        else
          let blocks_snapshot = List.map get_block (List.map (fun (b : Cfg.block) -> b.label) f.blocks) in
          let effects = collect_loop_effects summaries globals loop blocks_snapshot in
          if effects.has_call then ()
          else
            let loop_temps =
              List.fold_left
                (fun acc (block : Cfg.block) ->
                  if not (LabelSet.mem block.label loop) then acc
                  else
                    let acc =
                      List.fold_left
                        (fun acc instr ->
                          let acc = add_instr_use_temps acc instr in
                          match defs_temp instr with
                          | Some temp -> IntSet.add temp acc
                          | None -> acc)
                        acc block.body
                    in
                    add_term_use_temps acc block.term)
                IntSet.empty blocks_snapshot
            in
            (* A hoisted bound lives for the whole loop instead of only at the
               exit compare.  Be deliberately stricter than the raw number of
               caller-saved homes: hidden loops near register-pressure limits can
               lose more to one new spill than they save by removing a repeated
               [li].  The proven hot_local_loop_mix case has pressure=5, so this
               cap preserves the observed 69 -> 65 win while declining denser
               loops. *)
            let loop_pressure = IntSet.cardinal loop_temps in
            let max_safe_bound_hoist_pressure = 5 in
            if loop_pressure > max_safe_bound_hoist_pressure then (
              if debug_bound_hoist then
                Printf.eprintf
                  "loop-bound-hoist-skip func=%s header=%s pressure=%d limit=%d\n%!"
                  f.name header loop_pressure max_safe_bound_hoist_pressure)
            else
              let candidates =
                blocks_snapshot
                |> List.filter_map (fun (block : Cfg.block) ->
                     if not (LabelSet.mem block.label loop) then None
                     else
                       match block.term with
                       | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
                           let true_inside = LabelSet.mem if_true loop in
                           let false_inside = LabelSet.mem if_false loop in
                           if true_inside = false_inside then None
                           else (
                             match lhs, rhs with
                             | Tcg.Imm imm, Tcg.Temp _ when imm <> 0L ->
                                 Some (block.label, op, `Left imm, lhs, rhs, if_true, if_false)
                             | Tcg.Temp _, Tcg.Imm imm when imm <> 0L ->
                                 Some (block.label, op, `Right imm, lhs, rhs, if_true, if_false)
                             | _ -> None)
                       | Cfg.Jump _ | Cfg.BranchZero _ | Cfg.BranchNonZero _ | Cfg.Return _ -> None)
              in
              match candidates with
              | [ (branch_label, op, side, lhs, rhs, if_true, if_false) ] ->
                  let header_block = get_block header in
                  let outside_preds =
                    List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
                  in
                  (* Final-only and deliberately conservative: use an existing
                     direct preheader only.  This avoids changing loop topology
                     after the optimizer has reached its fixed point. *)
                  (match outside_preds with
                  | [ preheader_label ] ->
                      let preheader = get_block preheader_label in
                      if preheader.succs <> [ header ] then ()
                      else
                        let bound =
                          match side with
                          | `Left imm | `Right imm -> imm
                        in
                        let bound_temp = fresh_temp () in
                        update_block
                          { preheader with body = preheader.body @ [ Tcg.Move (bound_temp, Tcg.Imm bound) ] };
                        let branch_block = get_block branch_label in
                        let term =
                          match side with
                          | `Left _ ->
                              Cfg.BranchCompare
                                (op, Tcg.Temp bound_temp, rhs, if_true, if_false)
                          | `Right _ ->
                              Cfg.BranchCompare
                                (op, lhs, Tcg.Temp bound_temp, if_true, if_false)
                        in
                        update_block { branch_block with term; succs = Cfg.successors term };
                        if debug_bound_hoist then
                          Printf.eprintf
                            "loop-bound-hoist func=%s header=%s branch=%s imm=%Ld temp=t%d pressure=%d\n%!"
                            f.name header branch_label bound bound_temp loop_pressure;
                        changed := true
                  | [] | _ :: _ :: _ -> ())
              | [] | _ :: _ :: _ -> ())
      headers;
    if !changed then
      let blocks =
        List.map (fun (block : Cfg.block) -> get_block block.label) f.blocks
      in
      Cfg.rebuild_edges { f with temp_count = !next_temp; blocks }
    else f

let classify_loop_rotate_targets loop (term : Cfg.terminator) =
  match branch_term_outcomes term with
  | Some (first_label, second_label) ->
      let first_inside = LabelSet.mem first_label loop in
      let second_inside = LabelSet.mem second_label loop in
      if first_inside && not second_inside then Some (first_label, second_label)
      else if second_inside && not first_inside then Some (second_label, first_label)
      else None
  | None -> None

let loop_rotate_func (f : Cfg.func) =
  let next_guard_id = ref 0 in
  let fresh_guard_label () =
    let id = !next_guard_id in
    incr next_guard_id;
    Printf.sprintf ".L%s_rotate_guard_%d" f.label id
  in
  let rec apply (current : Cfg.func) =
    let block_map, loops, headers = discover_natural_loops current in
    if headers = [] then current
    else
      match
        List.find_map
          (fun header ->
            let header_block : Cfg.block = Hashtbl.find block_map header in
            let loop = table_find_or_empty loops header LabelSet.empty in
            let outside_preds =
              List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
            in
            let backedge_preds =
              List.filter (fun pred -> LabelSet.mem pred loop) header_block.preds
            in
            if
              header_block.body <> []
              || backedge_preds = []
              || (outside_preds = [] && header <> current.entry)
              || is_rotate_guard_label header
            then None
            else
              match classify_loop_rotate_targets loop header_block.term with
              | None -> None
              | Some (_inside_label, _exit_label) ->
                  let guard_label = fresh_guard_label () in
                  let guard_block =
                    {
                      Cfg.label = guard_label;
                      body = [];
                      term = header_block.term;
                      preds = [];
                      succs = Cfg.successors header_block.term;
                    }
                  in
                  let blocks =
                    let redirected_blocks =
                      List.map
                        (fun (block : Cfg.block) ->
                          if List.exists (fun pred -> pred = block.label) outside_preds then
                            let term =
                              rewrite_term_successor block.term ~from_label:header ~to_label:guard_label
                            in
                            { block with term; succs = Cfg.successors term }
                          else block)
                        current.blocks
                    in
                    List.fold_right
                      (fun (block : Cfg.block) acc ->
                        if block.label = header then guard_block :: block :: acc else block :: acc)
                      redirected_blocks []
                  in
                  let entry = if header = current.entry then guard_label else current.entry in
                  Some (Cfg.rebuild_edges { current with entry; blocks }))
          headers
      with
      | Some rotated -> apply rotated
      | None -> current
  in
  apply f

let strength_reduce_func (f : Cfg.func) =
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let _, def_blocks, def_instrs, multi_defs =
      analyze_temp_defs_of_blocks f.temp_count f.blocks
    in
    let current_blocks = Hashtbl.create (List.length f.blocks) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_block = get_block_exn current_blocks in
    let update_block (block : Cfg.block) =
      Hashtbl.replace current_blocks block.label block
    in
    let next_temp = ref f.temp_count in
    let fresh_temp () =
      let temp = !next_temp in
      incr next_temp;
      temp
    in
    let changed = ref false in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        let loop_defs = loop_defined_temps loop get_block in
        let loop_stable_phis =
          collect_loop_stable_phis header loop get_block def_blocks multi_defs def_instrs
        in
        let ivs = analyze_induction_vars header loop get_block loop_defs multi_defs def_instrs in
        List.iter
          (fun (iv : basic_induction_var) ->
            let derived_uses = Hashtbl.create 4 in
            List.iter
              (fun (block : Cfg.block) ->
                if LabelSet.mem block.label loop then
                  List.iteri
                    (fun index instr ->
                      match
                        derived_expr_of_instr
                          loop_defs loop_stable_phis multi_defs def_instrs iv.phi_temp instr
                      with
                      | Some (dst, key) ->
                          let uses = Option.value ~default:[] (Hashtbl.find_opt derived_uses key) in
                          Hashtbl.replace derived_uses key ((block.label, index, dst) :: uses)
                      | None -> ())
                    (get_block block.label).body)
              f.blocks;
            Hashtbl.iter
               (fun key uses ->
                if worthwhile_derived_key key uses then begin
                  changed := true;
                  let derived_phi = fresh_temp () in
                  List.iter
                    (fun (pred, src) ->
                      let pred_block = get_block pred in
                      let body = pred_block.body @ build_derived_init key derived_phi src in
                      update_block { pred_block with body })
                    iv.outside_inputs;
                  let delta = delta_of_derived_key iv.step key in
                  List.iter
                    (fun pred ->
                      let pred_block = get_block pred in
                      let body = pred_block.body @ build_derived_backedge_update derived_phi delta in
                      update_block { pred_block with body })
                    iv.backedge_preds;
                  List.iter
                    (fun (block : Cfg.block) ->
                      if LabelSet.mem block.label loop then
                        let current = get_block block.label in
                        let replacements = Hashtbl.create (List.length uses) in
                        List.iter
                          (fun (label, index, dst) ->
                            if label = current.label then Hashtbl.replace replacements index dst)
                          uses;
                        if Hashtbl.length replacements > 0 then
                          let body =
                            List.mapi
                              (fun index instr ->
                                match Hashtbl.find_opt replacements index with
                                | Some dst -> Tcg.Move (dst, Tcg.Temp derived_phi)
                                | None -> instr)
                              current.body
                          in
                          update_block { current with body })
                    f.blocks
                end)
              derived_uses)
          ivs)
      headers;
    if !changed then
      let ordered_labels = List.map (fun (block : Cfg.block) -> block.label) f.blocks in
      let blocks = List.map get_block ordered_labels in
      Cfg.rebuild_edges { f with temp_count = !next_temp; blocks }
    else f

let temp_use_counts blocks =
  let counts = Hashtbl.create 32 in
  let add_operand = function
    | Tcg.Temp temp ->
        let count = Option.value ~default:0 (Hashtbl.find_opt counts temp) in
        Hashtbl.replace counts temp (count + 1)
    | Tcg.Imm _ -> ()
  in
  let add_instr_uses = function
    | Tcg.Move (_, src)
    | Tcg.Un (_, _, src) ->
        add_operand src
    | Tcg.Bin (_, _, lhs, rhs) ->
        add_operand lhs;
        add_operand rhs
    | Tcg.Load _ -> ()
    | Tcg.Store (_, value) -> add_operand value
    | Tcg.Call (_, _, args) -> List.iter add_operand args
  in
  let add_term_uses = function
    | Cfg.Jump _ | Cfg.Return None -> ()
    | Cfg.BranchZero (cond, _, _)
    | Cfg.BranchNonZero (cond, _, _)
    | Cfg.Return (Some cond) ->
        add_operand cond
    | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
        add_operand lhs;
        add_operand rhs
  in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter add_instr_uses block.body;
      add_term_uses block.term)
    blocks;
  counts

let algebra_canonicalize_func (f : Cfg.func) =
  let _, _, def_instrs, multi_defs =
    analyze_temp_defs_of_blocks f.temp_count f.blocks
  in
  let use_counts = temp_use_counts f.blocks in
  let use_count temp =
    Option.value ~default:0 (Hashtbl.find_opt use_counts temp)
  in
  let add_i32 a b = i32 Int64.(add (i32 a) (i32 b)) in
  let sub_i32 a b = i32 Int64.(sub (i32 a) (i32 b)) in
  let mul_i32 a b = i32 Int64.(mul (i32 a) (i32 b)) in
  let neg_i32 value = i32 Int64.(neg (i32 value)) in
  let rec affine_of_operand seen = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp as operand ->
        if IntSet.mem temp seen || IntSet.mem temp multi_defs || use_count temp <> 1 then
          Some (operand, 1, 0L, false)
        else
          let seen = IntSet.add temp seen in
          match Hashtbl.find_opt def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) -> (
              match affine_of_operand seen src with
              | Some (base, sign, bias, _) -> Some (base, sign, bias, true)
              | None -> Some (operand, 1, 0L, false))
          | Some (Tcg.Un (_, UMinus, src)) -> (
              match affine_of_operand seen src with
              | Some (base, sign, bias, _) ->
                  Some (base, -sign, neg_i32 bias, true)
              | None -> Some (operand, 1, 0L, false))
          | Some (Tcg.Bin (_, Add, lhs, Tcg.Imm c))
          | Some (Tcg.Bin (_, Add, Tcg.Imm c, lhs)) -> (
              match affine_of_operand seen lhs with
              | Some (base, sign, bias, _) ->
                  Some (base, sign, add_i32 bias c, true)
              | None -> Some (operand, 1, 0L, false))
          | Some (Tcg.Bin (_, Sub, lhs, Tcg.Imm c)) -> (
              match affine_of_operand seen lhs with
              | Some (base, sign, bias, _) ->
                  Some (base, sign, sub_i32 bias c, true)
              | None -> Some (operand, 1, 0L, false))
          | Some (Tcg.Bin (_, Sub, Tcg.Imm c, rhs)) -> (
              match affine_of_operand seen rhs with
              | Some (base, sign, bias, _) ->
                  Some (base, -sign, sub_i32 c bias, true)
              | None -> Some (operand, 1, 0L, false))
          | Some (Tcg.Un _)
          | Some (Tcg.Bin _)
          | Some (Tcg.Load _)
          | Some (Tcg.Store _)
          | Some (Tcg.Call _)
          | None ->
              Some (operand, 1, 0L, false)
  in
  let rec scale_of_operand seen = function
    | Tcg.Imm _ -> None
    | Tcg.Temp temp as operand ->
        if IntSet.mem temp seen || IntSet.mem temp multi_defs || use_count temp <> 1 then
          Some (operand, 1L, false)
        else
          let seen = IntSet.add temp seen in
          match Hashtbl.find_opt def_instrs temp with
          | Some (Tcg.Move (_, src))
          | Some (Tcg.Un (_, UPlus, src)) -> (
              match scale_of_operand seen src with
              | Some (base, factor, _) -> Some (base, factor, true)
              | None -> Some (operand, 1L, false))
          | Some (Tcg.Un (_, UMinus, src)) -> (
              match scale_of_operand seen src with
              | Some (base, factor, _) ->
                  Some (base, neg_i32 factor, true)
              | None -> Some (operand, 1L, false))
          | Some (Tcg.Bin (_, Mul, lhs, Tcg.Imm c))
          | Some (Tcg.Bin (_, Mul, Tcg.Imm c, lhs)) -> (
              match scale_of_operand seen lhs with
              | Some (base, factor, _) ->
                  Some (base, mul_i32 factor c, true)
              | None -> Some (operand, 1L, false))
          | Some (Tcg.Un _)
          | Some (Tcg.Bin _)
          | Some (Tcg.Load _)
          | Some (Tcg.Store _)
          | Some (Tcg.Call _)
          | None ->
              Some (operand, 1L, false)
  in
  let build_affine dst (base, sign, bias) =
    if sign = 1 then
      if bias = 0L then Tcg.Move (dst, base)
      else Tcg.Bin (dst, Add, base, Tcg.Imm bias)
    else if bias = 0L then
      Tcg.Un (dst, UMinus, base)
    else
      Tcg.Bin (dst, Sub, Tcg.Imm bias, base)
  in
  let build_scale dst base factor =
    if factor = 0L then Tcg.Move (dst, Tcg.Imm 0L)
    else if factor = 1L then Tcg.Move (dst, base)
    else if factor = -1L then Tcg.Un (dst, UMinus, base)
    else Tcg.Bin (dst, Mul, base, Tcg.Imm factor)
  in
  let unique_def_of_operand = function
    | Tcg.Temp temp when not (IntSet.mem temp multi_defs) ->
        Hashtbl.find_opt def_instrs temp
    | Tcg.Temp _ | Tcg.Imm _ -> None
  in
  let cancel_add_sub dst lhs rhs =
    (* i32 arithmetic is modulo 2^32, so these cancellations remain valid
       even when the intermediate addition/subtraction wraps.  Only follow
       unique temporary definitions; phi/multi-definition temporaries are
       deliberately excluded. *)
    match unique_def_of_operand lhs with
    | Some (Tcg.Bin (_, Add, a, b)) when operand_equal rhs a ->
        Some (Tcg.Move (dst, b))
    | Some (Tcg.Bin (_, Add, a, b)) when operand_equal rhs b ->
        Some (Tcg.Move (dst, a))
    | _ -> (
        match unique_def_of_operand rhs with
        | Some (Tcg.Bin (_, Sub, a, b)) when operand_equal lhs a ->
            Some (Tcg.Move (dst, b))
        | _ -> None)
  in
  let cancel_sub_add dst lhs rhs =
    let from_mid mid other =
      match unique_def_of_operand mid with
      | Some (Tcg.Bin (_, Sub, a, b)) when operand_equal other b ->
          Some (Tcg.Move (dst, a))
      | _ -> None
    in
    match from_mid lhs rhs with
    | Some _ as rewritten -> rewritten
    | None -> from_mid rhs lhs
  in
  let rewrites = ref 0 in
  let cancellation_rewrites = ref 0 in
  let rewrite_instr instr =
    let initial = simplify_simple_instr instr in
    let rewritten =
      match initial with
      | Tcg.Bin (dst, Add, lhs, rhs) -> (
          match cancel_sub_add dst lhs rhs with
          | Some rewritten ->
              incr cancellation_rewrites;
              rewritten
          | None ->
              let lhs, rhs =
                match (lhs, rhs) with
                | Tcg.Imm c, other -> (other, Tcg.Imm c)
                | _ -> (lhs, rhs)
              in
              begin match rhs with
              | Tcg.Imm c -> (
                  match affine_of_operand IntSet.empty lhs with
                  | Some (base, sign, bias, true) ->
                      build_affine dst (base, sign, add_i32 bias c)
                  | Some _ | None -> Tcg.Bin (dst, Add, lhs, rhs))
              | Tcg.Temp _ -> Tcg.Bin (dst, Add, lhs, rhs)
              end)
      | Tcg.Bin (dst, Sub, lhs, rhs) -> (
          match cancel_add_sub dst lhs rhs with
          | Some rewritten ->
              incr cancellation_rewrites;
              rewritten
          | None -> (
              match (lhs, rhs) with
              | lhs, Tcg.Imm c -> (
                  match affine_of_operand IntSet.empty lhs with
                  | Some (base, sign, bias, true) ->
                      build_affine dst (base, sign, sub_i32 bias c)
                  | Some _ | None -> initial)
              | Tcg.Imm c, rhs -> (
                  match affine_of_operand IntSet.empty rhs with
                  | Some (base, sign, bias, true) ->
                      build_affine dst (base, -sign, sub_i32 c bias)
                  | Some _ | None -> initial)
              | Tcg.Temp _, Tcg.Temp _ -> initial))
      | Tcg.Bin (dst, Mul, lhs, rhs) ->
          let lhs, rhs =
            match (lhs, rhs) with
            | Tcg.Imm c, other -> (other, Tcg.Imm c)
            | _ -> (lhs, rhs)
          in
          begin match rhs with
          | Tcg.Imm c -> (
              match scale_of_operand IntSet.empty lhs with
              | Some (base, factor, true) ->
                  build_scale dst base (mul_i32 factor c)
              | Some _ | None -> Tcg.Bin (dst, Mul, lhs, rhs))
          | Tcg.Temp _ -> Tcg.Bin (dst, Mul, lhs, rhs)
          end
      | Tcg.Un (dst, UMinus, src) -> (
          match affine_of_operand IntSet.empty src with
          | Some (base, sign, bias, true) ->
              build_affine dst (base, -sign, neg_i32 bias)
          | Some _ | None -> initial)
      | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ ->
          initial
    in
    let rewritten = simplify_simple_instr rewritten in
    if rewritten <> instr then incr rewrites;
    rewritten
  in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let body = List.map rewrite_instr block.body in
        { block with body })
      f.blocks
  in
  if Sys.getenv_opt "TOYC_DEBUG_ALGEBRA" <> None then
    Printf.eprintf
      "algebra func=%s rewrites=%d cancellations=%d\n%!"
      f.name !rewrites !cancellation_rewrites;
  if !rewrites = 0 then f else Cfg.rebuild_edges { f with blocks }

type reassoc_first =
  | FirstVarPlusInv of Tcg.operand * Tcg.operand
  | FirstVarMinusInv of Tcg.operand * Tcg.operand
  | FirstInvMinusVar of Tcg.operand * Tcg.operand

type reassoc_second =
  | SecondMidPlusInv of Tcg.temp * Tcg.operand
  | SecondMidMinusInv of Tcg.temp * Tcg.operand
  | SecondInvMinusMid of Tcg.temp * Tcg.operand

let classify_reassoc_first invariant = function
  | Tcg.Bin (mid, Add, lhs, rhs) ->
      if invariant lhs && not (invariant rhs) then Some (mid, FirstVarPlusInv (rhs, lhs))
      else if not (invariant lhs) && invariant rhs then
        Some (mid, FirstVarPlusInv (lhs, rhs))
      else None
  | Tcg.Bin (mid, Sub, lhs, rhs) ->
      if not (invariant lhs) && invariant rhs then Some (mid, FirstVarMinusInv (lhs, rhs))
      else if invariant lhs && not (invariant rhs) then
        Some (mid, FirstInvMinusVar (lhs, rhs))
      else None
  | Tcg.Bin (_, (Mul | Div | Mod | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr), _, _) ->
      None
  | Tcg.Move _ | Tcg.Un _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> None

let classify_reassoc_second mid invariant = function
  | Tcg.Bin (dst, Add, lhs, rhs) when lhs = Tcg.Temp mid && invariant rhs ->
      Some (SecondMidPlusInv (dst, rhs))
  | Tcg.Bin (dst, Add, lhs, rhs) when rhs = Tcg.Temp mid && invariant lhs ->
      Some (SecondMidPlusInv (dst, lhs))
  | Tcg.Bin (dst, Sub, lhs, rhs) when lhs = Tcg.Temp mid && invariant rhs ->
      Some (SecondMidMinusInv (dst, rhs))
  | Tcg.Bin (dst, Sub, lhs, rhs) when rhs = Tcg.Temp mid && invariant lhs ->
      Some (SecondInvMinusMid (dst, lhs))
  | Tcg.Bin (_, (Mul | Div | Mod | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr), _, _) ->
      None
  | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> None

let build_reassoc_instrs mid first_shape second_shape =
  let inv_bin dst op lhs rhs = simplify_simple_instr (Tcg.Bin (dst, op, lhs, rhs)) in
  let add_mid dst variant = simplify_simple_instr (Tcg.Bin (dst, Add, variant, Tcg.Temp mid)) in
  let sub_mid_from dst variant =
    simplify_simple_instr (Tcg.Bin (dst, Sub, Tcg.Temp mid, variant))
  in
  let sub_variant_from dst variant =
    simplify_simple_instr (Tcg.Bin (dst, Sub, variant, Tcg.Temp mid))
  in
  match (first_shape, second_shape) with
  | FirstVarPlusInv (variant, inv1), SecondMidPlusInv (dst, inv2) ->
      Some (inv_bin mid Add inv1 inv2, add_mid dst variant)
  | FirstVarPlusInv (variant, inv1), SecondMidMinusInv (dst, inv2) ->
      Some (inv_bin mid Sub inv1 inv2, add_mid dst variant)
  | FirstVarPlusInv (variant, inv1), SecondInvMinusMid (dst, inv2) ->
      Some (inv_bin mid Sub inv2 inv1, sub_mid_from dst variant)
  | FirstVarMinusInv (variant, inv1), SecondMidPlusInv (dst, inv2) ->
      Some (inv_bin mid Sub inv2 inv1, add_mid dst variant)
  | FirstVarMinusInv (variant, inv1), SecondMidMinusInv (dst, inv2) ->
      Some (inv_bin mid Add inv1 inv2, sub_variant_from dst variant)
  | FirstVarMinusInv (variant, inv1), SecondInvMinusMid (dst, inv2) ->
      Some (inv_bin mid Add inv2 inv1, sub_mid_from dst variant)
  | FirstInvMinusVar (inv1, variant), SecondMidPlusInv (dst, inv2) ->
      Some (inv_bin mid Add inv1 inv2, sub_mid_from dst variant)
  | FirstInvMinusVar (inv1, variant), SecondMidMinusInv (dst, inv2) ->
      Some (inv_bin mid Sub inv1 inv2, sub_mid_from dst variant)
  | FirstInvMinusVar (inv1, variant), SecondInvMinusMid (dst, inv2) ->
      Some (inv_bin mid Sub inv2 inv1, add_mid dst variant)

let reassociate_loop_adds_func (f : Cfg.func) =
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let _, def_blocks, def_instrs, multi_defs =
      analyze_temp_defs_of_blocks f.temp_count f.blocks
    in
    let use_counts = temp_use_counts f.blocks in
    let current_blocks = Hashtbl.create (List.length f.blocks) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_block = get_block_exn current_blocks in
    let changed = ref false in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        let loop_defs = loop_defined_temps loop get_block in
        let loop_stable_phis =
          collect_loop_stable_phis header loop get_block def_blocks multi_defs def_instrs
        in
        let invariant operand =
          operand_loop_invariant
            loop_defs loop_stable_phis multi_defs def_instrs IntSet.empty operand
        in
        List.iter
          (fun (block : Cfg.block) ->
            if LabelSet.mem block.label loop then
              let current = get_block block.label in
              let single_use temp =
                Option.value ~default:0 (Hashtbl.find_opt use_counts temp) = 1
              in
              let try_reassociate first second =
                match classify_reassoc_first invariant first with
                | Some (mid, first_shape) when single_use mid -> (
                    match classify_reassoc_second mid invariant second with
                    | Some second_shape -> build_reassoc_instrs mid first_shape second_shape
                    | None -> None)
                | Some _ | None -> None
              in
              let rec rewrite = function
                | first :: second :: rest -> (
                    match try_reassociate first second with
                    | Some (first', second') ->
                        changed := true;
                        first' :: second' :: rewrite rest
                    | None -> first :: rewrite (second :: rest))
                | body -> body
              in
              Hashtbl.replace current_blocks current.label { current with body = rewrite current.body })
          f.blocks)
      headers;
    if !changed then
      let ordered_labels = List.map (fun (block : Cfg.block) -> block.label) f.blocks in
      let blocks = List.map get_block ordered_labels in
      Cfg.rebuild_edges { f with blocks }
    else f

let unswitch_max_blocks = 16
let unswitch_min_instrs = 12
let unswitch_min_memory_ops = 2
let unswitch_max_instrs = 96

let unswitch_loops_func _summaries _globals (f : Cfg.func) =
  let block_map, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let exception Applied of Cfg.func in
    let _, _, def_instrs, multi_defs =
      analyze_temp_defs_of_blocks f.temp_count f.blocks
    in
    try
      List.iter
        (fun header ->
          let loop = table_find_or_empty loops header LabelSet.empty in
          if is_unswitch_label header || LabelSet.exists is_unswitch_label loop then ()
          else
            let header_block : Cfg.block = Hashtbl.find block_map header in
            let outside_preds = List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds in
            if outside_preds = [] && header <> f.entry then ()
            else
              let loop_blocks =
                f.blocks
                |> List.filter (fun (block : Cfg.block) -> LabelSet.mem block.label loop)
              in
              let total_instrs =
                List.fold_left (fun acc (block : Cfg.block) -> acc + List.length block.body) 0 loop_blocks
              in
              let memory_ops = loop_memory_ops_count loop f.blocks in
              if
                List.length loop_blocks > unswitch_max_blocks
                || total_instrs > unswitch_max_instrs
                || total_instrs < unswitch_min_instrs
                || (memory_ops < unswitch_min_memory_ops && total_instrs < (2 * unswitch_min_instrs))
              then ()
              else
                let loop_defs = loop_defined_temps loop (get_block_exn block_map) in
                match
                  List.find_map
                    (fun (block : Cfg.block) ->
                      match (branch_term_outcomes block.term, rewrite_branch_term_before_loop loop_defs multi_defs def_instrs block.term) with
                      | Some (if_true, if_false), Some dispatch_term
                        when LabelSet.mem if_true loop && LabelSet.mem if_false loop ->
                          Some (block, if_true, if_false, dispatch_term)
                      | _ -> None)
                    loop_blocks
                with
                | None -> ()
                | Some (branch_block, if_true, if_false, dispatch_term) ->
                    let original_labels = List.map (fun (block : Cfg.block) -> block.label) f.blocks in
                    let current_blocks = Hashtbl.create (List.length f.blocks + (2 * List.length loop_blocks) + 1) in
                    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
                    let get_block = get_block_exn current_blocks in
                    let update_block (block : Cfg.block) =
                      Hashtbl.replace current_blocks block.label block
                    in
                    let clone_id = List.length loop_blocks + List.length outside_preds + List.length header_block.succs in
                    let dispatch_label =
                      Printf.sprintf ".L%s_unswitch_dispatch_%s_%d" f.label header clone_id
                    in
                    let true_map =
                      List.mapi
                        (fun index (block : Cfg.block) ->
                          ( block.label,
                            Printf.sprintf ".L%s_unswitch_t_%s_%d_%d" f.label header clone_id index ))
                        loop_blocks
                    in
                    let false_map =
                      List.mapi
                        (fun index (block : Cfg.block) ->
                          ( block.label,
                            Printf.sprintf ".L%s_unswitch_f_%s_%d_%d" f.label header clone_id index ))
                        loop_blocks
                    in
                    let rename label map =
                      match List.assoc_opt label map with
                      | Some renamed -> renamed
                      | None -> label
                    in
                    let true_header = rename header true_map in
                    let false_header = rename header false_map in
                    let dispatch_term = branch_term_with_targets dispatch_term true_header false_header in
                    let dispatch_block =
                      {
                        Cfg.label = dispatch_label;
                        body = [];
                        term = dispatch_term;
                        preds = [];
                        succs = Cfg.successors dispatch_term;
                      }
                    in
                    let clone_block map chosen_target (block : Cfg.block) =
                      let label = rename block.label map in
                      let term =
                        if block.label = branch_block.label then Cfg.Jump (rename chosen_target map)
                        else rewrite_term_labels (fun lbl -> rename lbl map) block.term
                      in
                      { block with label; term; preds = []; succs = Cfg.successors term }
                    in
                    let true_blocks = List.map (clone_block true_map if_true) loop_blocks in
                    let false_blocks = List.map (clone_block false_map if_false) loop_blocks in
                    let redirects = Hashtbl.create (List.length outside_preds) in
                    List.iter
                      (fun pred -> Hashtbl.add redirects (pred, header) dispatch_label)
                      outside_preds;
                    List.iter
                      (fun pred ->
                        let pred_block = get_block pred in
                        let term = redirect_successors pred redirects pred_block.term in
                        update_block { pred_block with term; succs = Cfg.successors term })
                      outside_preds;
                    Hashtbl.add current_blocks dispatch_label dispatch_block;
                    List.iter
                      (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block)
                      true_blocks;
                    List.iter
                      (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block)
                      false_blocks;
                    let new_blocks =
                      dispatch_label
                      :: List.map (fun (block : Cfg.block) -> block.label) true_blocks
                      @ List.map (fun (block : Cfg.block) -> block.label) false_blocks
                    in
                    let entry = if header = f.entry then dispatch_label else f.entry in
                    let blocks =
                      List.map get_block original_labels @ List.map get_block new_blocks
                    in
                    let unswitched = Cfg.rebuild_edges { f with entry; blocks } in
                    let reachable = reachable_labels unswitched.entry unswitched.blocks in
                    let blocks =
                      List.filter
                        (fun (block : Cfg.block) -> LabelSet.mem block.label reachable)
                        unswitched.blocks
                    in
                    raise (Applied (Cfg.rebuild_edges { unswitched with blocks })))
        headers;
      f
    with
    | Applied next -> next

let licm_func summaries globals (f : Cfg.func) =
  let _, loops, headers = discover_natural_loops f in
  if headers = [] then f
  else
    let current_blocks = Hashtbl.create (List.length f.blocks + List.length headers) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_block = get_block_exn current_blocks in
    let update_block (block : Cfg.block) =
      Hashtbl.replace current_blocks block.Cfg.label block
    in
    let current_block_list () = Hashtbl.fold (fun _ block acc -> block :: acc) current_blocks [] in
    let new_blocks_rev = ref [] in
    let preheader_id = ref 0 in
    let fresh_preheader_label () =
      let id = !preheader_id in
      incr preheader_id;
      Printf.sprintf ".L%s_licm_preheader_%d" f.label id
    in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        let header_block = get_block header in
        let outside_preds =
          List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
        in
        if outside_preds <> [] then begin
          let blocks_snapshot = current_block_list () in
          let loop_defs, def_blocks, def_instrs, multi_defs =
            analyze_temp_defs_of_blocks ~loop f.temp_count blocks_snapshot
          in
          let effects = collect_loop_effects summaries globals loop blocks_snapshot in
          let loop_stable_phis =
            collect_loop_stable_phis header loop get_block def_blocks multi_defs def_instrs
          in
          let invariant_keys = ref InstrKeySet.empty in
          let invariant_temps = ref IntSet.empty in
          let changed = ref true in
          while !changed do
            changed := false;
            List.iter
              (fun (block : Cfg.block) ->
                if LabelSet.mem block.label loop then (
                  let current = get_block block.label in
                  List.iteri
                    (fun index instr ->
                      let key = (current.label, index) in
                      if not (InstrKeySet.mem key !invariant_keys) then
                        match
                          licm_invariant_candidate
                            loop_defs
                            loop_stable_phis
                            multi_defs
                            def_instrs
                            !invariant_temps
                            effects
                            instr
                        with
                        | Some dst ->
                            invariant_keys := InstrKeySet.add key !invariant_keys;
                            invariant_temps := IntSet.add dst !invariant_temps;
                            changed := true
                        | None -> ())
                    current.body))
              f.blocks
          done;
          if not (InstrKeySet.is_empty !invariant_keys) then begin
            let scheduled_keys = ref InstrKeySet.empty in
            let ready_temps = ref IntSet.empty in
            let hoisted_rev = ref [] in
            let progress = ref true in
            while !progress do
              progress := false;
              List.iter
                (fun (block : Cfg.block) ->
                  if LabelSet.mem block.label loop then (
                    let current = get_block block.label in
                    List.iteri
                      (fun index instr ->
                        let key = (current.label, index) in
                        if InstrKeySet.mem key !invariant_keys
                           && not (InstrKeySet.mem key !scheduled_keys)
                        then
                          match
                            licm_invariant_candidate
                              loop_defs
                              loop_stable_phis
                              multi_defs
                              def_instrs
                              !ready_temps
                              effects
                              instr
                          with
                          | Some dst ->
                              hoisted_rev := instr :: !hoisted_rev;
                              scheduled_keys := InstrKeySet.add key !scheduled_keys;
                              ready_temps := IntSet.add dst !ready_temps;
                              progress := true
                          | None -> ())
                      current.body))
                f.blocks
            done;
            if not (InstrKeySet.is_empty !scheduled_keys) then begin
              let preheader_label =
                match outside_preds with
                | [ pred ] ->
                    let pred_block = get_block pred in
                    if pred_block.succs = [ header ] then pred else fresh_preheader_label ()
                | _ -> fresh_preheader_label ()
              in
              let created_preheader = not (Hashtbl.mem current_blocks preheader_label) in
              if created_preheader then begin
                let redirects = Hashtbl.create (List.length outside_preds) in
                List.iter
                  (fun pred -> Hashtbl.add redirects (pred, header) preheader_label)
                  outside_preds;
                List.iter
                  (fun pred ->
                    let pred_block = get_block pred in
                    let term = redirect_successors pred redirects pred_block.term in
                    update_block { pred_block with term; succs = Cfg.successors term })
                  outside_preds;
                let preheader =
                  {
                    Cfg.label = preheader_label;
                    body = [];
                    term = Cfg.Jump header;
                    preds = [];
                    succs = [ header ];
                  }
                in
                Hashtbl.add current_blocks preheader_label preheader;
                new_blocks_rev := preheader_label :: !new_blocks_rev
              end;
              let preheader = get_block preheader_label in
              let hoisted = List.rev !hoisted_rev in
              let body = gvn_rewrite_instrs summaries globals (preheader.body @ hoisted) in
              update_block { preheader with body };
              List.iter
                (fun (block : Cfg.block) ->
                  if LabelSet.mem block.label loop then
                    let current = get_block block.label in
                    let body =
                      List.mapi (fun index instr -> ((current.label, index), instr)) current.body
                      |> List.filter (fun (key, _) -> not (InstrKeySet.mem key !scheduled_keys))
                      |> List.map snd
                    in
                    update_block { current with body })
                f.blocks
            end
          end
        end)
      headers;
    let ordered_labels = List.map (fun (block : Cfg.block) -> block.label) f.blocks in
    let blocks =
      List.map get_block ordered_labels
      @ List.rev_map get_block !new_blocks_rev
    in
    Cfg.rebuild_edges { f with blocks }

let rewrite_branch_operand term operand =
  match term with
  | Cfg.BranchZero (Tcg.Temp _, if_zero, if_nonzero) ->
      if if_zero = if_nonzero then Cfg.Jump if_zero
      else Cfg.BranchZero (operand, if_zero, if_nonzero)
  | Cfg.BranchNonZero (Tcg.Temp _, if_nonzero, if_zero) ->
      if if_zero = if_nonzero then Cfg.Jump if_zero
      else Cfg.BranchNonZero (operand, if_nonzero, if_zero)
  | _ -> term

let invert_branch_on_operand term operand =
  match term with
  | Cfg.BranchZero (Tcg.Temp _, if_zero, if_nonzero) ->
      if if_zero = if_nonzero then Cfg.Jump if_zero
      else Cfg.BranchNonZero (operand, if_zero, if_nonzero)
  | Cfg.BranchNonZero (Tcg.Temp _, if_nonzero, if_zero) ->
      if if_zero = if_nonzero then Cfg.Jump if_zero
      else Cfg.BranchZero (operand, if_nonzero, if_zero)
  | _ -> term

let fold_compare_branch_term term op lhs rhs =
  match term with
  | Cfg.BranchZero (Tcg.Temp _, if_zero, if_nonzero)
  | Cfg.BranchNonZero (Tcg.Temp _, if_nonzero, if_zero) ->
      if if_zero = if_nonzero then Cfg.Jump if_zero
      else Cfg.BranchCompare (op, lhs, rhs, if_nonzero, if_zero)
  | _ -> term

let fold_branch_tails_func summaries globals (f : Cfg.func) =
  let live_in_t, _ = compute_liveness summaries globals f in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let live_out = live_out_t live_in_t block in
        match List.rev block.body with
        | Tcg.Move (dst, src) :: rest
          when not (IntSet.mem dst live_out) -> (
            match block.term with
            | Cfg.BranchZero (Tcg.Temp temp, _, _)
            | Cfg.BranchNonZero (Tcg.Temp temp, _, _)
              when temp = dst ->
                let term = rewrite_branch_operand block.term src in
                { block with body = List.rev rest; term; succs = Cfg.successors term }
            | _ -> block)
        | Tcg.Un (dst, UPlus, src) :: rest
          when not (IntSet.mem dst live_out) -> (
            match block.term with
            | Cfg.BranchZero (Tcg.Temp temp, _, _)
            | Cfg.BranchNonZero (Tcg.Temp temp, _, _)
              when temp = dst ->
                let term = rewrite_branch_operand block.term src in
                { block with body = List.rev rest; term; succs = Cfg.successors term }
            | _ -> block)
        | Tcg.Un (dst, UNot, src) :: rest
          when not (IntSet.mem dst live_out) -> (
            match block.term with
            | Cfg.BranchZero (Tcg.Temp temp, _, _)
            | Cfg.BranchNonZero (Tcg.Temp temp, _, _)
              when temp = dst ->
                let term = invert_branch_on_operand block.term src in
                { block with body = List.rev rest; term; succs = Cfg.successors term }
            | _ -> block)
        | Tcg.Bin (dst, op, lhs, rhs) :: rest
          when is_compare_binop op && not (IntSet.mem dst live_out) -> (
            match block.term with
            | Cfg.BranchZero (Tcg.Temp temp, _, _)
            | Cfg.BranchNonZero (Tcg.Temp temp, _, _)
              when temp = dst ->
                let term = fold_compare_branch_term block.term op lhs rhs in
                { block with body = List.rev rest; term; succs = Cfg.successors term }
            | _ -> block)
        | _ -> block)
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

let count_calls_in_func (f : Cfg.func) =
  List.fold_left
    (fun count (block : Cfg.block) ->
      List.fold_left
        (fun count instr ->
          match instr with
          | Tcg.Call _ -> count + 1
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ -> count)
        count block.body)
    0 f.blocks

let eliminate_dead_code_func ?removable_calls summaries globals return_globals (f : Cfg.func) =
  let calls_before =
    if Sys.getenv_opt "TOYC_DEBUG_DEAD_CALLS" <> None then Some (count_calls_in_func f)
    else None
  in
  let live_in_t, live_in_p =
    compute_liveness_with_return_globals ?removable_calls summaries globals return_globals f
  in
  let count_global_stores blocks =
    List.fold_left
      (fun count (block : Cfg.block) ->
        List.fold_left
          (fun count instr ->
            match instr with
            | Tcg.Store (Tcg.Global _, _) -> count + 1
            | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ ->
                count)
          count block.body)
      0 blocks
  in
  let before_global_stores =
    if Sys.getenv_opt "TOYC_DEBUG_GLOBAL_DSE" <> None then
      Some (count_global_stores f.blocks)
    else None
  in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let live_t_out =
          List.fold_left
            (fun acc succ ->
              IntSet.union acc (table_find_or_empty live_in_t succ IntSet.empty))
            IntSet.empty block.succs
        in
        let live_p_out =
          List.fold_left
            (fun acc succ ->
              PlaceSet.union acc (table_find_or_empty live_in_p succ PlaceSet.empty))
            PlaceSet.empty block.succs
        in
        let block, _, _ =
          scan_block ~return_globals ?removable_calls summaries globals block live_t_out live_p_out
        in
        { block with succs = Cfg.successors block.term })
      f.blocks
  in
  begin
    match before_global_stores with
    | Some before ->
        let after = count_global_stores blocks in
        if before <> after then
          Printf.eprintf
            "global-dse func=%s return_globals=%d/%d global_stores=%d->%d removed=%d\n%!"
            f.name (PlaceSet.cardinal return_globals) (PlaceSet.cardinal globals)
            before after (before - after)
    | None -> ()
  end;
  let result = Cfg.rebuild_edges { f with blocks } in
  begin
    match calls_before with
    | Some before ->
        let after = count_calls_in_func result in
        if after < before then
          Printf.eprintf
            "dead-call-dce func=%s calls=%d->%d removed=%d\n%!"
            f.name before after (before - after)
    | None -> ()
  end;
  result

let simplify_counted_loop_guards_func _summaries _globals (f : Cfg.func) =
  let block_map, loops, headers = discover_natural_loops f in
  let get_block = get_block_exn block_map in
  if headers = [] then f
  else
    let current_blocks = Hashtbl.create (List.length f.blocks) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_current = get_block_exn current_blocks in
    let def_instrs = temp_def_instrs_map f in
    let changed = ref false in
    Hashtbl.iter
      (fun header loop ->
        let loop_blocks = List.filter (fun (block : Cfg.block) -> LabelSet.mem block.label loop) f.blocks in
        let loop_defs = loop_defined_temps loop get_block in
        let multi_defs = multi_def_temps_of_blocks f.temp_count loop_blocks in
        let loop_stable_phis = collect_header_phi_temps header get_block in
        let _, control =
          analyze_counted_control header loop get_block loop_defs loop_stable_phis multi_defs def_instrs
        in
        match control with
        | None -> ()
        | Some info ->
            LabelSet.iter
              (fun label ->
                if label <> info.control_label then
                  let block : Cfg.block = get_current label in
                let fold_branch op lhs rhs if_true if_false =
                  let try_fold op lhs rhs =
                    match
                      ( iv_bias_of_operand_in_block block multi_defs def_instrs info.control_iv.phi_temp lhs,
                        operand_static_int64 loop_defs multi_defs def_instrs rhs )
                      with
                      | Some bias, Some constant -> (
                          match
                            compare_truth_from_range op (range_of_counted_iv_expr info.kind bias) constant
                          with
                          | Some true -> Some (Cfg.Jump if_true)
                          | Some false -> Some (Cfg.Jump if_false)
                          | None -> None)
                      | _ -> None
                  in
                  match try_fold op lhs rhs with
                  | Some term -> Some term
                  | None -> try_fold (swap_compare op) rhs lhs
                in
                match block.term with
                | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) -> (
                    match fold_branch op lhs rhs if_true if_false with
                    | Some term ->
                        changed := true;
                        Hashtbl.replace current_blocks label { block with term; succs = Cfg.successors term }
                    | None -> ())
                | Cfg.BranchZero (cond, if_zero, if_nonzero) -> (
                    match resolve_compare_operand_in_block block multi_defs def_instrs cond with
                    | Some (op, lhs, rhs) -> (
                        match fold_branch op lhs rhs if_nonzero if_zero with
                        | Some term ->
                            changed := true;
                            Hashtbl.replace current_blocks label { block with term; succs = Cfg.successors term }
                        | None -> ())
                    | None -> ())
                | Cfg.BranchNonZero (cond, if_nonzero, if_zero) -> (
                    match resolve_compare_operand_in_block block multi_defs def_instrs cond with
                    | Some (op, lhs, rhs) -> (
                        match fold_branch op lhs rhs if_nonzero if_zero with
                        | Some term ->
                            changed := true;
                            Hashtbl.replace current_blocks label { block with term; succs = Cfg.successors term }
                        | None -> ())
                    | None -> ())
                | Cfg.Jump _ | Cfg.Return _ -> ())
              loop)
      loops;
    if not !changed then f
    else
      let ordered_labels = List.map (fun (block : Cfg.block) -> block.label) f.blocks in
       let blocks = List.map get_current ordered_labels in
       Cfg.rebuild_edges { f with blocks }

let split_counted_diamond_loops_func _summaries _globals (f : Cfg.func) =
  let block_map, loops, headers = discover_natural_loops f in
  let next_temp = ref f.temp_count in
  let fresh_temp () =
    let temp = !next_temp in
    incr next_temp;
    temp
  in
  if headers = [] then f
  else
    let exception Applied of Cfg.func in
    let pure_scalar_block (block : Cfg.block) =
      List.for_all
        (function
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ -> true
          | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> false)
        block.body
    in
    let rec collapse_pure_scalar_connector loop seen label =
      if LabelSet.mem label seen || not (Hashtbl.mem block_map label) then None
      else
        let block : Cfg.block = Hashtbl.find block_map label in
        if not (LabelSet.mem block.label loop) then None
        else if not (pure_scalar_block block) then None
        else
          match block.succs with
          | [] -> Some block.label
           | [ next ] ->
               if transparent_loop_connector block then
                 collapse_pure_scalar_connector loop (LabelSet.add label seen) next
               else Some block.label
           | _ -> Some block.label
    in
    let outer_limit_of_kind loop_defs multi_defs def_instrs = function
      | CountUpLt (bound, bias) -> normalize_limit_operand loop_defs multi_defs def_instrs bound Int64.(neg bias)
      | CountUpLe (bound, bias) -> normalize_limit_operand loop_defs multi_defs def_instrs bound Int64.(sub 1L bias)
      | CountDownGt (bound, bias) -> normalize_limit_operand loop_defs multi_defs def_instrs bound Int64.(neg bias)
      | CountDownGe (bound, bias) -> normalize_limit_operand loop_defs multi_defs def_instrs bound Int64.(neg bias)
    in
    let normalized_limit_is_entry_invariant loop_defs = function
      | LimitConst _ -> true
      | LimitOperand (operand, _) -> (
          match operand with
          | Tcg.Imm _ -> true
          | Tcg.Temp temp -> not (IntSet.mem temp loop_defs))
    in
    let normalized_limit_is_const = function
      | LimitConst _ -> true
      | LimitOperand _ -> false
    in
    let normalized_limit_equal lhs rhs =
      match (lhs, rhs) with
      | LimitConst a, LimitConst b -> a = b
      | LimitOperand (Tcg.Imm a, delta_a), LimitOperand (Tcg.Imm b, delta_b) ->
          a = b && delta_a = delta_b
      | LimitOperand (Tcg.Temp a, delta_a), LimitOperand (Tcg.Temp b, delta_b) ->
          a = b && delta_a = delta_b
      | _ -> false
    in
    let materialize_adjusted_operand operand delta =
      match operand with
      | Tcg.Imm constant -> ([], Tcg.Imm Int64.(add constant delta))
      | _ when delta = 0L -> ([], operand)
      | _ ->
          let temp = fresh_temp () in
          ([ Tcg.Bin (temp, Add, operand, Tcg.Imm delta) ], Tcg.Temp temp)
    in
    let materialize_limit_operand = function
      | LimitConst bound -> ([], Tcg.Imm bound)
      | LimitOperand (operand, delta) -> materialize_adjusted_operand operand delta
    in
    let branch_with_rhs compare_op iv_temp rhs if_true if_false =
      Cfg.BranchCompare (compare_op, Tcg.Temp iv_temp, rhs, if_true, if_false)
    in
    let build_branch_for_limit compare_op iv_temp limit if_true if_false =
      match limit with
      | LimitConst bound ->
          ([], branch_with_rhs compare_op iv_temp (Tcg.Imm bound) if_true if_false)
      | LimitOperand (operand, delta) ->
          let body, rhs = materialize_adjusted_operand operand delta in
          (body, branch_with_rhs compare_op iv_temp rhs if_true if_false)
    in
    let build_branch_for_shifted_compare compare_op iv_temp operand bias if_true if_false =
      let body, rhs = materialize_adjusted_operand operand Int64.(neg bias) in
      (body, branch_with_rhs compare_op iv_temp rhs if_true if_false)
    in
    let loop_counts_up = function
      | CountUpLt _ | CountUpLe _ -> true
      | CountDownGt _ | CountDownGe _ -> false
    in
    let first_phase_uses_true_branch kind split_op =
      if loop_counts_up kind then
        match split_op with
        | Lt | Le -> true
        | Gt | Ge -> false
        | Eq | Ne | Add | Sub | Mul | Div | Mod | LAnd | LOr -> false
      else
        match split_op with
        | Gt | Ge -> true
        | Lt | Le -> false
        | Eq | Ne | Add | Sub | Mul | Div | Mod | LAnd | LOr -> false
    in
    let prefix_limit_of_split loop_defs multi_defs def_instrs kind split_op operand bias =
      let delta =
        match kind with
        | CountUpLt _ -> (
            match split_op with
            | Lt | Ge -> Int64.neg bias
            | Le | Gt -> Int64.(sub 1L bias)
            | Eq | Ne | Add | Sub | Mul | Div | Mod | LAnd | LOr -> 0L)
        | CountUpLe _ -> (
            match split_op with
            | Lt | Ge -> Int64.(sub (neg bias) 1L)
            | Le | Gt -> Int64.neg bias
            | Eq | Ne | Add | Sub | Mul | Div | Mod | LAnd | LOr -> 0L)
        | CountDownGt _ -> (
            match split_op with
            | Gt | Le -> Int64.neg bias
            | Ge | Lt -> Int64.(sub (neg bias) 1L)
            | Eq | Ne | Add | Sub | Mul | Div | Mod | LAnd | LOr -> 0L)
        | CountDownGe _ -> (
            match split_op with
            | Gt | Le -> Int64.(add (neg bias) 1L)
            | Ge | Lt -> Int64.neg bias
            | Eq | Ne | Add | Sub | Mul | Div | Mod | LAnd | LOr -> 0L)
      in
      match split_op with
      | Lt | Le | Gt | Ge -> normalize_limit_operand loop_defs multi_defs def_instrs operand delta
      | Eq | Ne | Add | Sub | Mul | Div | Mod | LAnd | LOr -> None
    in
    let should_split_loop loop_blocks outer_limit prefix_limit =
      let block_count = List.length loop_blocks in
      let instr_count =
        List.fold_left (fun acc (block : Cfg.block) -> acc + List.length block.body) 0 loop_blocks
      in
      let branchy_blocks =
        List.fold_left
          (fun acc (block : Cfg.block) ->
            match block.term with
            | Cfg.BranchZero _ | Cfg.BranchNonZero _ | Cfg.BranchCompare _ -> acc + 1
            | Cfg.Jump _ | Cfg.Return _ -> acc)
          0 loop_blocks
      in
      let const_benefit =
        normalized_limit_is_const outer_limit || normalized_limit_is_const prefix_limit
      in
      block_count <= 10
      && instr_count <= 28
      && branchy_blocks <= 4
      && (const_benefit || instr_count <= 18)
    in
    let relabel_func_prefix prefix (func : Cfg.func) =
      let mapping = Hashtbl.create (List.length func.blocks) in
      let blocks =
        List.mapi
          (fun index (block : Cfg.block) ->
            let label = Printf.sprintf ".L%s_%s_%d" f.label prefix index in
            Hashtbl.add mapping block.label label;
            { block with label })
          func.blocks
      in
      let rename label = Option.value ~default:label (Hashtbl.find_opt mapping label) in
      let blocks =
        List.map
          (fun (block : Cfg.block) ->
            let term = rewrite_term_labels rename block.term in
            { block with term; succs = Cfg.successors term })
          blocks
      in
      { func with entry = rename func.entry; blocks }
    in
    let _, _, def_instrs, multi_defs =
      analyze_temp_defs_of_blocks f.temp_count f.blocks
    in
    try
      List.iter
        (fun header ->
          let loop = table_find_or_empty loops header LabelSet.empty in
          let header_block : Cfg.block = Hashtbl.find block_map header in
          let loop_blocks =
            f.blocks |> List.filter (fun (block : Cfg.block) -> LabelSet.mem block.label loop)
          in
          let loop_defs = loop_defined_temps loop (get_block_exn block_map) in
          let loop_stable_phis = collect_header_phi_temps header (Hashtbl.find block_map) in
          let _, control =
            analyze_counted_control
              header loop (Hashtbl.find block_map) loop_defs loop_stable_phis multi_defs def_instrs
          in
          match control with
          | None -> ()
          | Some info ->
              let control_block : Cfg.block = Hashtbl.find block_map info.control_label in
              let split_block =
                if info.control_label = header then
                  Hashtbl.find block_map info.inside_label
                else control_block
              in
              let header_term_for_limit =
                match info.kind with
                | CountUpLt _ -> Lt
                | CountUpLe _ -> Le
                | CountDownGt _ -> Gt
                | CountDownGe _ -> Ge
              in
              match branch_term_outcomes split_block.term with
                | Some (branch_a, branch_b)
                  when LabelSet.mem branch_a loop && LabelSet.mem branch_b loop -> (
                     let branch_a_block : Cfg.block = Hashtbl.find block_map branch_a in
                     let branch_b_block : Cfg.block = Hashtbl.find block_map branch_b in
                     if
                       not
                         ( pure_scalar_block split_block
                         && pure_scalar_block branch_a_block
                         && pure_scalar_block branch_b_block )
                       || branch_a = branch_b
                     then ()
                     else
                       match
                         ( collapse_pure_scalar_connector loop LabelSet.empty branch_a,
                           collapse_pure_scalar_connector loop LabelSet.empty branch_b,
                           branch_compare_shape_in_block split_block multi_defs def_instrs split_block.term,
                           outer_limit_of_kind loop_defs multi_defs def_instrs info.kind )
                       with
                       | Some join_a, Some join_b, Some (split_op0, lhs, rhs, if_true, if_false), Some outer_limit
                         when join_a = join_b -> (
                           let join_label = join_a in
                           let split_info =
                             match
                               ( iv_bias_of_operand_in_block
                                   split_block
                                   multi_defs
                                   def_instrs
                                   info.control_iv.phi_temp
                                   lhs,
                                 resolve_operand_before_loop loop_defs multi_defs def_instrs rhs )
                             with
                             | Some bias, Some rhs_operand ->
                                 Some (split_op0, rhs_operand, bias, if_true, if_false)
                             | _ -> (
                                 match
                                   ( iv_bias_of_operand_in_block
                                       split_block
                                       multi_defs
                                       def_instrs
                                       info.control_iv.phi_temp
                                       rhs,
                                     resolve_operand_before_loop loop_defs multi_defs def_instrs lhs )
                                 with
                                 | Some bias, Some lhs_operand ->
                                     Some (swap_compare split_op0, lhs_operand, bias, if_true, if_false)
                                 | _ -> None)
                           in
                           match split_info with
                           | Some (split_op, split_operand, split_bias, if_true, if_false) ->
                               begin
                                 match
                                   prefix_limit_of_split
                                     loop_defs
                                     multi_defs
                                     def_instrs
                                     info.kind
                                     split_op
                                     split_operand
                                     split_bias
                                 with
                                 | Some prefix_limit
                                   when normalized_limit_is_entry_invariant loop_defs outer_limit
                                        && normalized_limit_is_entry_invariant loop_defs prefix_limit
                                        && not (normalized_limit_equal outer_limit prefix_limit)
                                        && should_split_loop loop_blocks outer_limit prefix_limit ->
                                   let first_uses_true =
                                     first_phase_uses_true_branch info.kind split_op
                                   in
                                   let first_branch =
                                     if first_uses_true then if_true else if_false
                                   in
                                   let second_branch =
                                     if first_uses_true then if_false else if_true
                                   in
                                   let before_bridge_label =
                                     Printf.sprintf ".L%s_split_bridge_%s" f.label header
                                   in
                                   let entry_dispatch_label =
                                     Printf.sprintf ".L%s_split_entry_%s" f.label header
                                   in
                                   let split_dispatch_label =
                                     Printf.sprintf ".L%s_split_dispatch_%s" f.label header
                                   in
                                   let limit_dispatch_label =
                                     Printf.sprintf ".L%s_split_limit_dispatch_%s" f.label header
                                   in
                                   let limit_take_outer_label =
                                     Printf.sprintf ".L%s_split_limit_outer_%s" f.label header
                                   in
                                   let limit_take_prefix_label =
                                     Printf.sprintf ".L%s_split_limit_prefix_%s" f.label header
                                   in
                                   let pre_limit_temp = fresh_temp () in
                                   let clone_loop prefix header_rhs exit_target split_term_builder =
                                     let blocks =
                                       List.map
                                         (fun (block : Cfg.block) ->
                                           if block.label = header then
                                             let term =
                                               branch_with_rhs
                                                 header_term_for_limit
                                                 info.control_iv.phi_temp
                                                 header_rhs
                                                 info.inside_label
                                                 exit_target
                                             in
                                             {
                                               block with
                                               body = [];
                                               term;
                                               succs = Cfg.successors term;
                                             }
                                           else if block.label = split_block.label then
                                             let body, term =
                                               split_term_builder first_branch second_branch
                                             in
                                             {
                                               block with
                                               body;
                                               term;
                                               succs = Cfg.successors term;
                                             }
                                           else block)
                                         loop_blocks
                                     in
                                     relabel_func_prefix prefix
                                       (Cfg.rebuild_edges { f with entry = header; blocks })
                                   in
                                   let outer_limit_body, outer_limit_rhs =
                                     materialize_limit_operand outer_limit
                                   in
                                   let prefix_limit_body, prefix_limit_rhs =
                                     materialize_limit_operand prefix_limit
                                   in
                                   let before_func =
                                     clone_loop "split_pre" (Tcg.Temp pre_limit_temp) before_bridge_label
                                       (fun first_branch _second_branch ->
                                         ([], Cfg.Jump first_branch))
                                   in
                                   let after_func =
                                     clone_loop "split_post" outer_limit_rhs info.exit_label
                                       (fun _first_branch second_branch ->
                                         ([], Cfg.Jump second_branch))
                                   in
                                   let entry_dispatch_body, entry_dispatch_term =
                                     build_branch_for_limit
                                       header_term_for_limit
                                       info.control_iv.phi_temp
                                       outer_limit
                                       split_dispatch_label
                                       info.exit_label
                                   in
                                   let split_dispatch_body, split_dispatch_term =
                                     if first_uses_true then
                                       build_branch_for_shifted_compare
                                         split_op
                                         info.control_iv.phi_temp
                                         split_operand
                                         split_bias
                                         limit_dispatch_label
                                         after_func.entry
                                     else
                                       build_branch_for_shifted_compare
                                         split_op
                                         info.control_iv.phi_temp
                                         split_operand
                                         split_bias
                                         after_func.entry
                                         limit_dispatch_label
                                   in
                                   let limit_choose_body =
                                     outer_limit_body @ prefix_limit_body
                                   in
                                   let limit_choose_term =
                                     if loop_counts_up info.kind then
                                       Cfg.BranchCompare
                                         (Lt, outer_limit_rhs, prefix_limit_rhs, limit_take_outer_label, limit_take_prefix_label)
                                     else
                                       Cfg.BranchCompare
                                         (Gt, outer_limit_rhs, prefix_limit_rhs, limit_take_outer_label, limit_take_prefix_label)
                                   in
                                   let entry_dispatch_block =
                                     {
                                       Cfg.label = entry_dispatch_label;
                                       body = entry_dispatch_body;
                                       term = entry_dispatch_term;
                                       preds = [];
                                       succs = Cfg.successors entry_dispatch_term;
                                     }
                                   in
                                   let split_dispatch_block =
                                     {
                                       Cfg.label = split_dispatch_label;
                                       body = split_dispatch_body;
                                       term = split_dispatch_term;
                                       preds = [];
                                       succs = Cfg.successors split_dispatch_term;
                                     }
                                   in
                                   let limit_dispatch_block =
                                     {
                                       Cfg.label = limit_dispatch_label;
                                       body = limit_choose_body;
                                       term = limit_choose_term;
                                       preds = [];
                                       succs = Cfg.successors limit_choose_term;
                                     }
                                   in
                                   let limit_take_outer_block =
                                     {
                                       Cfg.label = limit_take_outer_label;
                                       body = [ Tcg.Move (pre_limit_temp, outer_limit_rhs) ];
                                       term = Cfg.Jump before_func.entry;
                                       preds = [];
                                       succs = [ before_func.entry ];
                                     }
                                   in
                                   let limit_take_prefix_block =
                                     {
                                       Cfg.label = limit_take_prefix_label;
                                       body = [ Tcg.Move (pre_limit_temp, prefix_limit_rhs) ];
                                       term = Cfg.Jump before_func.entry;
                                       preds = [];
                                       succs = [ before_func.entry ];
                                     }
                                   in
                                   let bridge_block =
                                     {
                                       Cfg.label = before_bridge_label;
                                       body = [];
                                       term = Cfg.Jump after_func.entry;
                                       preds = [];
                                       succs = [ after_func.entry ];
                                     }
                                   in
                                   let outside_preds =
                                     List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
                                   in
                                   let redirects = Hashtbl.create (List.length outside_preds) in
                                   List.iter
                                     (fun pred ->
                                       Hashtbl.add redirects (pred, header) entry_dispatch_label)
                                     outside_preds;
                                   let base_blocks =
                                     f.blocks
                                     |> List.filter (fun (block : Cfg.block) ->
                                            not (LabelSet.mem block.label loop))
                                     |> List.map (fun (block : Cfg.block) ->
                                            if
                                              List.exists
                                                (fun pred -> pred = block.label)
                                                outside_preds
                                            then
                                              let term =
                                                redirect_successors block.label redirects block.term
                                              in
                                              { block with term; succs = Cfg.successors term }
                                            else block)
                                   in
                                   let entry =
                                     if header = f.entry then entry_dispatch_label else f.entry
                                   in
                                   if Sys.getenv_opt "TOYC_DEBUG_DIAMOND_SPLIT" <> None then
                                     Printf.eprintf
                                       "diamond-split func=%s header=%s pre=%s post=%s limit=%s bridge=%s\n%!"
                                       f.name header before_func.entry after_func.entry
                                       limit_dispatch_label before_bridge_label;
                                   let blocks =
                                     base_blocks
                                     @ [
                                         entry_dispatch_block;
                                         split_dispatch_block;
                                         limit_dispatch_block;
                                         limit_take_outer_block;
                                         limit_take_prefix_block;
                                         bridge_block;
                                       ]
                                     @ before_func.blocks @ after_func.blocks
                                   in
                                   let _ = join_label in
                                   raise
                                     (Applied
                                        (Cfg.rebuild_edges
                                           {
                                             f with
                                             entry;
                                             temp_count = !next_temp;
                                             blocks;
                                           }))
                                 | Some _ | None -> ()
                               end
                           | None -> ())
                       | _ -> ())
                | Some _ | None -> ())
        headers;
      f
    with
    | Applied next -> next

type func_metrics = {
  block_count : int;
  instr_count : int;
  temp_count : int;
}

type opt_profile = {
  name : string;
  max_rounds : int;
}

let metrics_of_func (f : Cfg.func) =
  let instr_count =
    List.fold_left (fun acc (block : Cfg.block) -> acc + List.length block.body) 0 f.blocks
  in
  { block_count = List.length f.blocks; instr_count; temp_count = f.temp_count }

let format_metrics { block_count; instr_count; temp_count } =
  Printf.sprintf "blocks=%d instrs=%d temps=%d" block_count instr_count temp_count

let choose_opt_profile metrics =
  if
    metrics.block_count >= 96
    || metrics.instr_count >= 480
    || metrics.temp_count >= 256
  then
    {
      name = "huge";
      max_rounds = 5;
    }
  else if
    metrics.block_count >= 48
    || metrics.instr_count >= 240
    || metrics.temp_count >= 128
  then
    {
      name = "large";
      max_rounds = 5;
    }
  else if
    metrics.block_count >= 24
    || metrics.instr_count >= 120
    || metrics.temp_count >= 64
  then
    {
      name = "medium";
      max_rounds = 5;
    }
  else
    {
      name = "full";
      max_rounds = 8;
    }

let stage_round_enabled profile round stage =
  match profile.name with
  | "huge" -> (
      match stage with
      | "split_reductions" | "unswitch" -> round <= 2
      | "diamond_split" | "full_unroll" | "unroll2" | "rotate" | "gvn2" -> round <= 1
      | _ -> true)
  | "large" -> (
      match stage with
      | "split_reductions" | "unswitch" -> round <= 3
      | "diamond_split" -> round <= 2
      | "full_unroll" | "unroll2" | "rotate" | "gvn2" -> round <= 4
      | _ -> true)
  | "medium" -> (
      match stage with
      | "split_reductions" | "unswitch" -> round <= 2
      | "diamond_split" -> round <= 2
      | "full_unroll" | "unroll2" | "rotate" -> round <= 3
      | _ -> true)
  | _ -> (
      match stage with
      | "diamond_split" -> round <= 2
      | _ -> true)

let optimize_func global_init summaries globals return_globals removable_calls (f : Cfg.func) =
  let promoted = f |> mem2reg_func |> promote_globals_func summaries globals in
  let canonical = loop_canonicalize_func summaries globals promoted in
  let base_metrics = metrics_of_func f in
  let promoted_metrics = metrics_of_func promoted in
  let profile = choose_opt_profile base_metrics in
  let debug_stop_after = Sys.getenv_opt "TOYC_DEBUG_STOP_AFTER" in
  let debug_pass_times = Sys.getenv_opt "TOYC_DEBUG_PASS_TIMES" <> None in
  let debug_opt_profile = debug_pass_times || Sys.getenv_opt "TOYC_DEBUG_OPT_PROFILE" <> None in
  let exception StopPass of Cfg.func in
  let stop_after stage current =
    match debug_stop_after with
    | Some target when target = stage -> raise (StopPass current)
    | Some _ | None -> current
  in
  let run_stage round ?(enabled = true) stage pass current =
    if not enabled then begin
      if debug_pass_times then
        Printf.eprintf "pass-time func=%s round=%d stage=%s skipped profile=%s\n%!"
          promoted.name round stage profile.name;
      stop_after stage current
    end else
      let before_metrics = if debug_pass_times then Some (metrics_of_func current) else None in
      let start_time = if debug_pass_times then Sys.time () else 0.0 in
      let candidate =
        try pass current with
        | Failure message when has_prefix "internal missing block: " message ->
            if debug_pass_times then
              Printf.eprintf
                "pass-time func=%s round=%d stage=%s recovered_missing_block=%s\n%!"
                promoted.name round stage message;
            current
      in
      (* Stage-local CFG correctness guard.
         A loop/CFG transform must never be allowed to poison all later stages.
         If one pass creates a terminator whose target block no longer exists,
         discard only that pass and continue from the last valid CFG. *)
      let next =
        if cfg_targets_valid candidate then candidate
        else begin
          debug_cfg_validation
            (Printf.sprintf "round=%d:%s" round stage)
            candidate;
          if Sys.getenv_opt "TOYC_DEBUG_CFG_VALIDATE" <> None then
            Printf.eprintf
              "cfg-stage-reject func=%s round=%d stage=%s\n%!"
              promoted.name round stage;
          current
        end
      in
      if debug_pass_times then begin
        let elapsed_ms = (Sys.time () -. start_time) *. 1000.0 in
        let before_metrics =
          match before_metrics with
          | Some metrics -> metrics
          | None -> metrics_of_func current
        in
        let after_metrics = metrics_of_func next in
        Printf.eprintf
          "pass-time func=%s round=%d stage=%s changed=%b ms=%.3f %s -> %s\n%!"
          promoted.name round stage (next <> current) elapsed_ms
          (format_metrics before_metrics) (format_metrics after_metrics)
      end;
      stop_after stage next
  in
  if debug_opt_profile then
    Printf.eprintf
      "opt-profile func=%s profile=%s rounds=%d base=(%s) promoted=(%s)\n%!"
      promoted.name profile.name profile.max_rounds
      (format_metrics base_metrics) (format_metrics promoted_metrics);
  let step round func =
    try
      let after_canon =
        run_stage round "canonicalize"
          (loop_canonicalize_func summaries globals)
          func
      in
      let after_simplify0 = run_stage round "simplify0" simplify_cfg_func after_canon in
      let after_const1 =
        run_stage round "const1"
          (const_propagate_func global_init summaries globals)
          after_simplify0
      in
      let after_algebra1 =
        run_stage round "algebra1" algebra_canonicalize_func after_const1
      in
      let after_sr = run_stage round "sr" strength_reduce_func after_algebra1 in
      let after_gvn1 = run_stage round "gvn1" (gvn_func summaries globals) after_sr in
      let after_dce1 =
        run_stage round "dce1" (eliminate_dead_code_func ~removable_calls summaries globals return_globals) after_gvn1
      in
      let after_reassoc = run_stage round "reassoc" reassociate_loop_adds_func after_dce1 in
      let after_licm = run_stage round "licm" (licm_func summaries globals) after_reassoc in
      let after_unswitch =
        run_stage round
          ~enabled:(stage_round_enabled profile round "unswitch")
          "unswitch"
          (unswitch_loops_func summaries globals)
          after_licm
      in
      let after_const2 =
        run_stage round "const2"
          (const_propagate_func global_init summaries globals)
          after_unswitch
      in
      let after_algebra2 =
        run_stage round "algebra2" algebra_canonicalize_func after_const2
      in
      let after_gvn2 =
        run_stage round "gvn2"
          (gvn_func summaries globals)
          after_algebra2
      in
      let after_dce2 =
        run_stage round "dce2" (eliminate_dead_code_func ~removable_calls summaries globals return_globals) after_gvn2
      in
      let after_dead_loops =
        run_stage round "dead_loops" (eliminate_dead_loops_func summaries globals) after_dce2
      in
      let after_fold =
        run_stage round "fold" (fold_branch_tails_func summaries globals) after_dead_loops
      in
      let after_thread1 = run_stage round "thread1" thread_and_prune_func after_fold in
      let after_canon2 =
        run_stage round "canonicalize2"
          (loop_canonicalize_func summaries globals)
          after_thread1
      in
      let after_simplify2 = run_stage round "simplify2" simplify_cfg_func after_canon2 in
      let after_loop_guards =
        run_stage round "loop_guards"
          (simplify_counted_loop_guards_func summaries globals)
          after_simplify2
      in
      let after_const3 =
        run_stage round "const3"
          (const_propagate_func global_init summaries globals)
          after_loop_guards
      in
      let after_dce3 =
        run_stage round "dce3" (eliminate_dead_code_func ~removable_calls summaries globals return_globals) after_const3
      in
      let after_fold4 =
        run_stage round "fold4" (fold_branch_tails_func summaries globals) after_dce3
      in
      let after_thread4 = run_stage round "thread4" thread_and_prune_func after_fold4 in
      let after_canon3 =
        run_stage round "canonicalize3"
          (loop_canonicalize_func summaries globals)
          after_thread4
      in
      let after_simplify3 = run_stage round "simplify3" simplify_cfg_func after_canon3 in
      let after_diamond_split =
        run_stage round
          ~enabled:(stage_round_enabled profile round "diamond_split")
          "diamond_split"
          (split_counted_diamond_loops_func summaries globals)
          after_simplify3
      in
      let after_split =
        run_stage round
          ~enabled:(stage_round_enabled profile round "split_reductions")
          "split_reductions"
          (extract_counted_reductions_func summaries globals)
          after_diamond_split
      in
      let after_counted =
        run_stage round "counted_loops"
          (eliminate_counted_loops_func summaries globals)
          after_split
      in
      let after_full_unroll =
        run_stage round
          ~enabled:(stage_round_enabled profile round "full_unroll")
          "full_unroll"
          (full_unroll_counted_loops_func summaries globals)
          after_counted
      in
      let after_unroll =
        run_stage round
          ~enabled:(stage_round_enabled profile round "unroll2")
          "unroll2"
          (unroll_counted_loops_x2_func summaries globals)
          after_full_unroll
      in
      let after_thread2 = run_stage round "thread2" thread_and_prune_func after_unroll in
      let after_fold2 =
        run_stage round "fold2" (fold_branch_tails_func summaries globals) after_thread2
      in
      let after_rotate =
        run_stage round
          ~enabled:(stage_round_enabled profile round "rotate")
          "rotate"
          loop_rotate_func after_fold2
      in
      let after_thread3 = run_stage round "thread3" thread_and_prune_func after_rotate in
      let after_fold3 =
        run_stage round "fold3" (fold_branch_tails_func summaries globals) after_thread3
      in
      after_fold3
    with
    | StopPass current -> current
  in
  let rec loop round fuel current =
    if fuel = 0 then current
    else
      let next = step round current in
      if next = current then current else loop (round + 1) (fuel - 1) next
  in
  match debug_stop_after with
  | Some "mem2reg" -> promoted
  | Some _ -> loop 1 profile.max_rounds canonical
  | None ->
      let optimized = loop 1 profile.max_rounds canonical in
      (* Keep the early mem2reg conservative so downstream CFG/loop transforms
         see the same stable shape as step24.  After all iterative transforms
         have settled, run a final optimistic loop-phi mem2reg: provisional
         loop-header phis can now bootstrap loop-carried locals without feeding
         the new phi/edge-copy CFG back into rotate/split/unroll passes. *)
      let late_promoted = mem2reg_func ~optimistic_loop_phi:true optimized in
      if Sys.getenv_opt "TOYC_DEBUG_LATE_MEM2REG" <> None then begin
        let count_local_accesses (func : Cfg.func) =
          List.fold_left
            (fun count (block : Cfg.block) ->
              List.fold_left
                (fun count instr ->
                  match instr with
                  | Tcg.Load (_, Tcg.Local _) | Tcg.Store (Tcg.Local _, _) -> count + 1
                  | _ -> count)
                count block.body)
            0 func.blocks
        in
        let before_locals = count_local_accesses optimized in
        let after_locals = count_local_accesses late_promoted in
        if before_locals <> after_locals || optimized.temp_count <> late_promoted.temp_count then
          Printf.eprintf
            "late-mem2reg func=%s local-accesses=%d->%d temps=%d->%d\n%!"
            optimized.name before_locals after_locals optimized.temp_count
            late_promoted.temp_count
      end;
      (* IMPORTANT: run late algebra BEFORE copy coalescing.  Late mem2reg
         deliberately creates fresh, mostly single-definition/single-use temp
         chains.  [algebra_canonicalize_func] can safely follow those chains,
         but coalescing first can merge unrelated definitions onto one temp and
         make the canonicalizer reject them as multi-def/use-heavy. *)
      let late_algebra = algebra_canonicalize_func late_promoted in
      let late_dce =
        eliminate_dead_code_func ~removable_calls summaries globals return_globals late_algebra
      in
      let late_coalesced = copy_coalesce_func summaries globals late_dce in
      if Sys.getenv_opt "TOYC_DEBUG_LATE_ALGEBRA" <> None then begin
        let before = metrics_of_func late_promoted in
        let after_algebra = metrics_of_func late_algebra in
        let after_dce = metrics_of_func late_coalesced in
        if late_coalesced <> late_promoted then
          Printf.eprintf
            "late-algebra func=%s instrs=%d->%d->%d temps=%d->%d\n%!"
            late_promoted.name before.instr_count after_algebra.instr_count
            after_dce.instr_count before.temp_count after_dce.temp_count
      end;
      let with_hoisted_loop_bounds =
        hoist_unrolled_loop_branch_immediates_func summaries globals late_coalesced
      in
      let final_candidate =
        final_linear_merge_func with_hoisted_loop_bounds
      in
      if cfg_targets_valid final_candidate then final_candidate
      else begin
        debug_cfg_validation "final-candidate" final_candidate;
        (* Correctness guard: never hand codegen a CFG containing a terminator
           whose target block was removed by a late transform.  Prefer the
           closest valid pre-final form so successful loop-phi promotion is
           retained whenever possible. *)
        let fallbacks =
          [
            ("pre-final-merge", with_hoisted_loop_bounds);
            ("late-coalesced", late_coalesced);
            ("pre-late-mem2reg", optimized);
            ("canonical", canonical);
            ("promoted", promoted);
            ("original", f);
          ]
        in
        let rec choose = function
          | [] -> f
          | (stage, candidate) :: rest ->
              if cfg_targets_valid candidate then begin
                if Sys.getenv_opt "TOYC_DEBUG_CFG_VALIDATE" <> None then
                  Printf.eprintf "cfg-fallback func=%s stage=%s\n%!"
                    f.name stage;
                candidate
              end else begin
                debug_cfg_validation stage candidate;
                choose rest
              end
        in
        choose fallbacks
      end


(* -------------------------------------------------------------------------- *)
(* Safe dead pure-call elimination                                            *)
(* -------------------------------------------------------------------------- *)

let func_has_direct_divmod (f : Cfg.func) =
  List.exists
    (fun (block : Cfg.block) ->
      List.exists
        (function
          | Tcg.Bin (_, (Div | Mod), _, _) -> true
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ ->
              false)
        block.body)
    f.blocks

let direct_callee_labels (f : Cfg.func) =
  List.fold_left
    (fun acc (block : Cfg.block) ->
      List.fold_left
        (fun acc instr ->
          match instr with
          | Tcg.Call (_, callee, _) -> LabelSet.add callee acc
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ -> acc)
        acc block.body)
    LabelSet.empty f.blocks

let strict_unit_counted_control = function
  | Some (info : counted_loop_info) -> (
      match info.kind with
      | CountUpLt (_, bias) ->
          info.control_iv.step = 1L && bias = 0L
      | CountDownGt (_, bias) ->
          info.control_iv.step = -1L && bias = 0L
      | CountUpLe _ | CountDownGe _ ->
          false)
  | None -> false

let cfg_acyclic_ignoring_edges (f : Cfg.func) ignored =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block)
    f.blocks;
  let color = Hashtbl.create (List.length f.blocks) in
  let rec visit label =
    match Hashtbl.find_opt color label with
    | Some 1 -> false
    | Some 2 -> true
    | Some _ | None ->
        Hashtbl.replace color label 1;
        let ok =
          match Hashtbl.find_opt block_map label with
          | None -> false
          | Some (block : Cfg.block) ->
              List.for_all
                (fun succ ->
                  if Hashtbl.mem ignored (label, succ) then true
                  else visit succ)
                block.succs
        in
        if ok then Hashtbl.replace color label 2;
        ok
  in
  visit f.entry

let func_cycles_provably_terminate summaries globals (f : Cfg.func) =
  (* Analysis-only SSA view.  It is never emitted and never enters the normal
     loop-transform pipeline; it merely exposes loop-carried induction vars. *)
  let view =
    f
    |> mem2reg_func ~optimistic_loop_phi:true
    |> loop_canonicalize_func summaries globals
  in
  if not (cfg_targets_valid view) then false
  else
    let block_map, loops, headers = discover_natural_loops view in
    let get_block = get_block_exn block_map in
    let safe_headers = Hashtbl.create (max 8 (List.length headers)) in
    List.iter
      (fun header ->
        let loop = table_find_or_empty loops header LabelSet.empty in
        let _, _, _, _, _, _, control =
          analyze_counted_loop header loop get_block view.temp_count view.blocks
        in
        Hashtbl.replace safe_headers header (strict_unit_counted_control control))
      headers;

    let doms = compute_dominators view in
    let ignored_backedges = Hashtbl.create 16 in
    let every_backedge_safe =
      List.for_all
        (fun (block : Cfg.block) ->
          List.for_all
            (fun succ ->
              if LabelSet.mem succ (table_find_or_empty doms block.label LabelSet.empty) then
                match Hashtbl.find_opt safe_headers succ with
                | Some true ->
                    Hashtbl.replace ignored_backedges (block.label, succ) true;
                    true
                | Some false | None -> false
              else true)
            block.succs)
        view.blocks
    in
    every_backedge_safe && cfg_acyclic_ignoring_edges view ignored_backedges

let compute_provably_terminating_funcs summaries globals funcs =
  let structural = Hashtbl.create (max 8 (List.length funcs)) in
  let known_funcs = Hashtbl.create (max 8 (List.length funcs)) in
  List.iter (fun (f : Cfg.func) -> Hashtbl.replace known_funcs f.label true) funcs;

  List.iter
    (fun (f : Cfg.func) ->
      let direct_calls_known =
        LabelSet.for_all (fun callee -> Hashtbl.mem known_funcs callee) (direct_callee_labels f)
      in
      let base =
        direct_calls_known
        && not (func_has_direct_divmod f)
        && func_cycles_provably_terminate summaries globals f
      in
      Hashtbl.replace structural f.label base)
    funcs;

  (* Least fixed point: recursion is therefore rejected unless it has already
     been removed by tail-recursion elimination into a provably counted loop. *)
  let terminating = Hashtbl.create (max 8 (List.length funcs)) in
  List.iter (fun (f : Cfg.func) -> Hashtbl.replace terminating f.label false) funcs;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (f : Cfg.func) ->
        let base =
          match Hashtbl.find_opt structural f.label with
          | Some value -> value
          | None -> false
        in
        let callees_ok =
          LabelSet.for_all
            (fun callee ->
              match Hashtbl.find_opt terminating callee with
              | Some true -> true
              | Some false | None -> false)
            (direct_callee_labels f)
        in
        let next = base && callees_ok in
        let prev =
          match Hashtbl.find_opt terminating f.label with
          | Some value -> value
          | None -> false
        in
        if next <> prev then begin
          Hashtbl.replace terminating f.label next;
          changed := true
        end)
      funcs
  done;
  terminating

let compute_dead_call_removable_funcs summaries globals funcs =
  let terminating = compute_provably_terminating_funcs summaries globals funcs in
  let removable = Hashtbl.create (max 8 (List.length funcs)) in
  List.iter
    (fun (f : Cfg.func) ->
      let terminates =
        match Hashtbl.find_opt terminating f.label with
        | Some value -> value
        | None -> false
      in
      let writes_globals = call_written_globals summaries globals f.label in
      let can_remove = terminates && PlaceSet.is_empty writes_globals in
      Hashtbl.replace removable f.label can_remove;
      if Sys.getenv_opt "TOYC_DEBUG_DEAD_CALLS" <> None then
        Printf.eprintf
          "dead-call-summary func=%s terminates=%b writes_globals=%d removable=%b\n%!"
          f.name terminates (PlaceSet.cardinal writes_globals) can_remove)
    funcs;
  removable


(* -------------------------------------------------------------------------- *)
(* Late trivial-call folding                                                  *)
(*                                                                            *)
(* DCE can turn a formerly complicated helper into a side-effect-free          *)
(* straight-line function that merely returns a constant or one of its         *)
(* arguments.  AST inlining has already happened by then, so without a late    *)
(* interprocedural cleanup the caller still pays the full call/RA-frame cost.  *)
(*                                                                            *)
(* Recognize only extremely safe callees: after jump-threading/final merging    *)
(* there must be exactly one reachable block, no Store/Call/global Load, no     *)
(* Div/Mod, and the return must symbolically reduce to a constant or parameter. *)
(* -------------------------------------------------------------------------- *)

type trivial_return_summary =
  | TrivialConst of int64
  | TrivialArg of int

type trivial_value =
  | TvConst of int64
  | TvArg of int

let trivial_value_of_operand env = function
  | Tcg.Imm value -> Some (TvConst (i32 value))
  | Tcg.Temp temp -> IntMap.find_opt temp env

let trivial_return_summary_of_func (f : Cfg.func) =
  let analysis_view =
    f
    |> thread_and_prune_func
    |> simplify_cfg_func
    |> final_linear_merge_func
    |> thread_and_prune_func
  in
  let reachable = reachable_labels analysis_view.entry analysis_view.blocks in
  let blocks =
    List.filter
      (fun (block : Cfg.block) -> LabelSet.mem block.label reachable)
      analysis_view.blocks
  in
  match blocks with
  | [ (block : Cfg.block) ] when block.label = analysis_view.entry ->
      let param_index_by_local = Hashtbl.create (List.length f.params) in
      List.iteri
        (fun index (param : Tcg.var) ->
          Hashtbl.replace param_index_by_local param.id index)
        f.params;
      let rec scan env = function
        | [] -> Some env
        | instr :: rest -> (
            match instr with
            | Tcg.Move (dst, src) -> (
                match trivial_value_of_operand env src with
                | Some value -> scan (IntMap.add dst value env) rest
                | None -> None)
            | Tcg.Un (dst, op, src) -> (
                match trivial_value_of_operand env src with
                | Some (TvConst value) -> (
                    match fold_unop op value with
                    | Some value -> scan (IntMap.add dst (TvConst value) env) rest
                    | None -> None)
                | Some (TvArg _) | None -> None)
            | Tcg.Bin (_, (Div | Mod), _, _) ->
                (* Even if constant-foldable, keep the proof deliberately
                   conservative around potentially trapping operators. *)
                None
            | Tcg.Bin (dst, op, lhs, rhs) -> (
                match
                  (trivial_value_of_operand env lhs, trivial_value_of_operand env rhs)
                with
                | Some (TvConst lhs), Some (TvConst rhs) -> (
                    match fold_binop op lhs rhs with
                    | Some value -> scan (IntMap.add dst (TvConst value) env) rest
                    | None -> None)
                | _ -> None)
            | Tcg.Load (dst, Tcg.Local local) -> (
                match Hashtbl.find_opt param_index_by_local local with
                | Some index -> scan (IntMap.add dst (TvArg index) env) rest
                | None -> None)
            | Tcg.Load (_, Tcg.Global _)
            | Tcg.Store _
            | Tcg.Call _ ->
                None)
      in
      begin
        match scan IntMap.empty block.body with
        | None -> None
        | Some env -> (
            match block.term with
            | Cfg.Return (Some operand) -> (
                match trivial_value_of_operand env operand with
                | Some (TvConst value) -> Some (TrivialConst value)
                | Some (TvArg index) -> Some (TrivialArg index)
                | None -> None)
            | Cfg.Return None
            | Cfg.Jump _
            | Cfg.BranchZero _
            | Cfg.BranchNonZero _
            | Cfg.BranchCompare _ ->
                None)
      end
  | _ -> None

let build_trivial_return_table funcs =
  let table = Hashtbl.create (max 8 (List.length funcs)) in
  List.iter
    (fun (f : Cfg.func) ->
      match trivial_return_summary_of_func f with
      | None -> ()
      | Some summary ->
          Hashtbl.replace table f.label summary;
          if Sys.getenv_opt "TOYC_DEBUG_TRIVIAL_CALLS" <> None then
            let summary_text =
              match summary with
              | TrivialConst value -> Printf.sprintf "const:%Ld" value
              | TrivialArg index -> Printf.sprintf "arg:%d" index
            in
            Printf.eprintf
              "trivial-call-summary func=%s summary=%s\n%!"
              f.name summary_text)
    funcs;
  table

let rewrite_trivial_calls_func table (f : Cfg.func) =
  let changed = ref false in
  let replaced = ref 0 in
  let rewrite_instr = function
    | Tcg.Call (dst, callee, args) as instr -> (
        match Hashtbl.find_opt table callee with
        | None -> Some instr
        | Some summary -> (
            match dst with
            | None ->
                changed := true;
                incr replaced;
                None
            | Some dst -> (
                let replacement =
                  match summary with
                  | TrivialConst value ->
                      Some (Tcg.Move (dst, Tcg.Imm value))
                  | TrivialArg index -> (
                      match List.nth_opt args index with
                      | Some operand -> Some (Tcg.Move (dst, operand))
                      | None -> None)
                in
                match replacement with
                | Some instr ->
                    changed := true;
                    incr replaced;
                    Some (simplify_simple_instr instr)
                | None -> Some instr)))
    | instr -> Some instr
  in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        { block with body = List.filter_map rewrite_instr block.body })
      f.blocks
  in
  let result =
    if !changed then Cfg.rebuild_edges { f with blocks }
    else f
  in
  if !changed && Sys.getenv_opt "TOYC_DEBUG_TRIVIAL_CALLS" <> None then
    Printf.eprintf
      "trivial-call-fold func=%s replaced=%d\n%!"
      f.name !replaced;
  result

let cleanup_after_trivial_call_fold
    global_init summaries globals return_globals removable_calls
    (f : Cfg.func) =
  let candidate =
    f
    |> const_propagate_func global_init summaries globals
    |> algebra_canonicalize_func
    |> eliminate_dead_code_func ~removable_calls summaries globals return_globals
    |> fold_branch_tails_func summaries globals
    |> thread_and_prune_func
    |> simplify_cfg_func
    |> final_linear_merge_func
  in
  if cfg_targets_valid candidate then candidate
  else begin
    debug_cfg_validation "late-trivial-call-cleanup" candidate;
    f
  end

let fold_trivial_calls_program
    global_init summaries globals return_global_demands removable_calls
    (funcs : Cfg.func list) =
  let rec iterate fuel current =
    if fuel = 0 then current
    else
      let table = build_trivial_return_table current in
      if Hashtbl.length table = 0 then current
      else
        let changed = ref false in
        let next =
          List.map
            (fun (f : Cfg.func) ->
              let rewritten = rewrite_trivial_calls_func table f in
              if rewritten <> f then changed := true;
              if rewritten = f then f
              else
                let return_globals =
                  match Hashtbl.find_opt return_global_demands f.label with
                  | Some return_globals -> return_globals
                  | None -> globals
                in
                cleanup_after_trivial_call_fold
                  global_init summaries globals return_globals removable_calls
                  rewritten)
            current
        in
        if not !changed || next = current then current
        else iterate (fuel - 1) next
  in
  (* A few waves are enough for chains such as main -> f -> g, where g becomes
     trivial first and f becomes trivial only after its call is folded. *)
  iterate 4 funcs

let optimize_cfg (analysis : Semant.analysis) (cfg : Cfg.program) =
  incr analysis_cache_generation;
  last_liveness_cache := None;
  last_dominator_cache := None;
  let cfg = { Cfg.funcs = List.map tailrec_elim_func cfg.funcs } in
  let global_init, globals =
    List.fold_left
      (fun (init, set) (g : Semant.global_decl) ->
        let place = Tcg.Global g.label in
        (PlaceMap.add place (CpConst g.init) init, PlaceSet.add place set))
      (PlaceMap.empty, PlaceSet.empty) analysis.globals
  in
  let summaries = compute_func_summaries globals cfg.funcs in
  let removable_calls =
    compute_dead_call_removable_funcs summaries globals cfg.funcs
  in
  let return_global_demands =
    compute_return_global_demands summaries globals cfg.funcs
  in
  let funcs_rev =
    List.fold_left
      (fun acc (f : Cfg.func) ->
        let return_globals =
          match Hashtbl.find_opt return_global_demands f.label with
          | Some return_globals -> return_globals
          | None -> globals
        in
        let optimized =
          optimize_func global_init summaries globals return_globals removable_calls f
        in
        optimized :: acc)
      [] cfg.funcs
  in
  let optimized_funcs = List.rev funcs_rev in
  let optimized_funcs =
    fold_trivial_calls_program
      global_init summaries globals return_global_demands removable_calls
      optimized_funcs
  in
  { Cfg.funcs = optimized_funcs }
