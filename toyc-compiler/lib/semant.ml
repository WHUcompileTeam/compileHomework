open Ast

exception Error of string

module StringMap = Map.Make (String)

type func_sig = {
  ret : typ;
  arity : int;
  label : string;
}

type global_decl = {
  name : string;
  label : string;
  is_const : bool;
  init : int64;
}

type analysis = {
  program : program;
  globals : global_decl list;
  funcs : func_sig StringMap.t;
}

type value_info = {
  is_const : bool;
  const_value : int64 option;
}

type expr_ty =
  | EInt
  | EVoid

type env = {
  funcs : func_sig StringMap.t;
  mutable scopes : value_info StringMap.t list;
  mutable loop_depth : int;
  current_ret : typ;
  current_func : string;
}

let func_label name = if name = "main" then "main" else "fn_" ^ name

let global_label name = "glob_" ^ name

let truth n = n <> 0L

let bool_int b = if b then 1L else 0L

let int32_modulus = 0x1_0000_0000L
let int32_sign_bit = 0x8000_0000L
let int32_mask = 0xFFFF_FFFFL

let i32 value =
  let masked = Int64.logand value int32_mask in
  if masked >= int32_sign_bit then Int64.sub masked int32_modulus else masked

let err msg = raise (Error msg)

let loc_msg loc msg = Printf.sprintf "%d:%d: %s" loc.line loc.col msg

let eval_binop op a b =
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

let rec eval_const_expr consts = function
  | Int n -> Some (i32 n)
  | Var name -> StringMap.find_opt name consts
  | Call _ -> None
  | Unary (op, e) -> (
      match eval_const_expr consts e with
      | None -> None
      | Some v -> (
          match op with
          | UPlus -> Some (i32 v)
          | UMinus -> Some (i32 (Int64.neg (i32 v)))
          | UNot -> Some (bool_int (not (truth (i32 v))))))
  | Binary (LAnd, a, b) -> (
      match eval_const_expr consts a with
      | Some 0L -> Some 0L
      | Some _ -> Option.map (fun v -> bool_int (truth v)) (eval_const_expr consts b)
      | None -> None)
  | Binary (LOr, a, b) -> (
      match eval_const_expr consts a with
      | Some v when truth v -> Some 1L
      | Some _ -> Option.map (fun v -> bool_int (truth v)) (eval_const_expr consts b)
      | None -> None)
  | Binary (op, a, b) -> (
      match (eval_const_expr consts a, eval_const_expr consts b) with
      | Some av, Some bv -> eval_binop op av bv
      | _ -> None)

let push_scope env = env.scopes <- StringMap.empty :: env.scopes

let pop_scope env =
  match env.scopes with
  | _ :: rest -> env.scopes <- rest
  | [] -> err "internal semantic scope underflow"

let add_name env (ident : Ast.ident) info =
  match env.scopes with
  | scope :: rest ->
      if StringMap.mem ident.name scope then
        err (loc_msg ident.loc ("duplicate declaration of " ^ ident.name));
      env.scopes <- StringMap.add ident.name info scope :: rest
  | [] -> err "internal semantic empty scope"

let find_name env name =
  let rec loop = function
    | [] -> None
    | scope :: rest -> (
        match StringMap.find_opt name scope with
        | Some info -> Some info
        | None -> loop rest)
  in
  loop env.scopes

let rec eval_const_expr_env env = function
  | Int n -> Some (i32 n)
  | Var name -> (
      match find_name env name with
      | Some { const_value = Some v; _ } -> Some v
      | _ -> None)
  | Call _ -> None
  | Unary (op, e) -> (
      match eval_const_expr_env env e with
      | None -> None
      | Some v -> (
          match op with
          | UPlus -> Some (i32 v)
          | UMinus -> Some (i32 (Int64.neg (i32 v)))
          | UNot -> Some (bool_int (not (truth (i32 v))))))
  | Binary (LAnd, a, b) -> (
      match eval_const_expr_env env a with
      | Some 0L -> Some 0L
      | Some _ -> Option.map (fun v -> bool_int (truth v)) (eval_const_expr_env env b)
      | None -> None)
  | Binary (LOr, a, b) -> (
      match eval_const_expr_env env a with
      | Some v when truth v -> Some 1L
      | Some _ -> Option.map (fun v -> bool_int (truth v)) (eval_const_expr_env env b)
      | None -> None)
  | Binary (op, a, b) -> (
      match (eval_const_expr_env env a, eval_const_expr_env env b) with
      | Some av, Some bv -> eval_binop op av bv
      | _ -> None)

let expect_int where = function
  | EInt -> ()
  | EVoid -> err (where ^ " cannot use a void expression")

let rec check_expr env = function
  | Int _ -> EInt
  | Var name -> (
      match find_name env name with
      | Some _ -> EInt
      | None -> err ("use of undeclared identifier " ^ name))
  | Unary (_, e) ->
      expect_int "unary operator" (check_expr env e);
      EInt
  | Binary (_, a, b) ->
      expect_int "binary operator left operand" (check_expr env a);
      expect_int "binary operator right operand" (check_expr env b);
      EInt
  | Call (name, args) -> (
      match StringMap.find_opt name env.funcs with
      | None -> err ("call to unknown or not-yet-declared function " ^ name)
      | Some f ->
          let argc = List.length args in
          if argc <> f.arity then
            err
              (Printf.sprintf "function %s expects %d arguments but got %d" name
                 f.arity argc);
          List.iter
            (fun arg -> expect_int ("argument of " ^ name) (check_expr env arg))
            args;
          match f.ret with
          | TInt -> EInt
          | TVoid -> EVoid)

let check_const_init env (d : Ast.decl) =
  match eval_const_expr_env env d.init with
  | Some v -> v
  | None ->
      err
        (loc_msg d.ident.loc
           ("initializer of const " ^ d.ident.name
          ^ " must be compile-time constant"))

let add_decl env consts (d : Ast.decl) =
  let ty = check_expr env d.init in
  expect_int ("initializer of " ^ d.ident.name) ty;
  let const_value = if d.is_const then Some (check_const_init env d) else None in
  add_name env d.ident { is_const = d.is_const; const_value };
  match const_value with
  | Some v -> StringMap.add d.ident.name v consts
  | None -> consts

let rec may_break_current_loop = function
  | Break -> true
  | Continue -> false
  | Block stmts -> List.exists may_break_current_loop stmts
  | If (_, t, e) ->
      may_break_current_loop t
      || Option.value (Option.map may_break_current_loop e) ~default:false
  | While _ -> false
  | Empty | Expr _ | Assign _ | Decl _ | Return _ -> false

let rec stmt_returns = function
  | Return _ -> true
  | Block stmts -> stmts_return stmts
  | If (_, then_s, Some else_s) -> stmt_returns then_s && stmt_returns else_s
  | While (Int v, body) when truth v ->
      stmt_returns body && not (may_break_current_loop body)
  | _ -> false

and stmts_return = function
  | [] -> false
  | s :: rest -> stmt_returns s || stmts_return rest

let rec check_stmt env consts = function
  | Block stmts ->
      push_scope env;
      let consts' = check_stmts env consts stmts in
      pop_scope env;
      consts'
  | Empty -> consts
  | Expr e ->
      ignore (check_expr env e);
      consts
  | Assign (name, rhs) -> (
      match find_name env name with
      | None -> err ("assignment to undeclared identifier " ^ name)
      | Some info ->
          if info.is_const then err ("assignment to const identifier " ^ name);
          expect_int ("right-hand side of assignment to " ^ name) (check_expr env rhs);
          consts)
  | Decl d -> add_decl env consts d
  | If (cond, then_s, else_s) ->
      expect_int "if condition" (check_expr env cond);
      ignore (check_stmt env consts then_s);
      Option.iter (fun s -> ignore (check_stmt env consts s)) else_s;
      consts
  | While (cond, body) ->
      expect_int "while condition" (check_expr env cond);
      env.loop_depth <- env.loop_depth + 1;
      ignore (check_stmt env consts body);
      env.loop_depth <- env.loop_depth - 1;
      consts
  | Break ->
      if env.loop_depth = 0 then err "break outside loop";
      consts
  | Continue ->
      if env.loop_depth = 0 then err "continue outside loop";
      consts
  | Return None ->
      (match env.current_ret with
      | TVoid -> ()
      | TInt -> err ("function " ^ env.current_func ^ " must return an int value"));
      consts
  | Return (Some e) ->
      (match env.current_ret with
      | TInt -> expect_int "return value" (check_expr env e)
      | TVoid -> err ("void function " ^ env.current_func ^ " cannot return a value"));
      consts

and check_stmts env consts stmts =
  List.fold_left (fun c s -> check_stmt env c s) consts stmts

let check_func global_scope funcs (f : Ast.func) =
  let env =
    {
      funcs;
      scopes = [ StringMap.empty; global_scope ];
      loop_depth = 0;
      current_ret = f.ret;
      current_func = f.name.name;
    }
  in
  List.iter
    (fun p -> add_name env p { is_const = false; const_value = None })
    f.params;
  ignore (check_stmts env StringMap.empty f.body);
  match f.ret with
  | TInt ->
      if not (stmts_return f.body) then
        err
          (loc_msg f.name.loc
             ("int function " ^ f.name.name
            ^ " may finish without returning a value"))
  | TVoid -> ()

let add_global_name global_names (ident : Ast.ident) kind =
  if StringMap.mem ident.name global_names then
    err (loc_msg ident.loc ("duplicate global name " ^ ident.name));
  StringMap.add ident.name kind global_names

let analyze program =
  let globals = ref [] in
  let funcs = ref StringMap.empty in
  let global_names = ref StringMap.empty in
  let global_scope = ref StringMap.empty in
  let global_consts = ref StringMap.empty in
  let visible_funcs = ref StringMap.empty in
  let register_global_decl (d : Ast.decl) =
    global_names := add_global_name !global_names d.ident "global";
    let init =
      match eval_const_expr !global_consts d.init with
      | Some v -> v
      | None ->
          err
            (loc_msg d.ident.loc
               ("global initializer for " ^ d.ident.name
              ^ " must be compile-time constant"))
    in
    let info =
      { is_const = d.is_const; const_value = if d.is_const then Some init else None }
    in
    global_scope := StringMap.add d.ident.name info !global_scope;
    if d.is_const then global_consts := StringMap.add d.ident.name init !global_consts;
    globals :=
      {
        name = d.ident.name;
        label = global_label d.ident.name;
        is_const = d.is_const;
        init;
      }
      :: !globals
  in
  let register_func (f : Ast.func) =
    global_names := add_global_name !global_names f.name "function";
    let sig_ =
      { ret = f.ret; arity = List.length f.params; label = func_label f.name.name }
    in
    funcs := StringMap.add f.name.name sig_ !funcs;
    visible_funcs := StringMap.add f.name.name sig_ !visible_funcs;
    check_func !global_scope !visible_funcs f
  in
  List.iter
    (function
      | TopDecl d -> register_global_decl d
      | FuncDef f -> register_func f)
    program;
  let main =
    match StringMap.find_opt "main" !funcs with
    | Some f -> f
    | None -> err "program must define int main()"
  in
  (match (main.ret, main.arity) with
  | TInt, 0 -> ()
  | _ -> err "main must have type int main()");
  { program; globals = List.rev !globals; funcs = !funcs }
