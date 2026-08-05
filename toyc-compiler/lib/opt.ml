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

let fold_unop op v =
  match op with
  | UPlus -> Some v
  | UMinus -> Some (Int64.neg v)
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
      | _ -> Tcg.Bin (dst, op, lhs, rhs))
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

let normalize_bin_operands op lhs rhs =
  if is_commutative_binop op && Stdlib.compare lhs rhs > 0 then (rhs, lhs)
  else (lhs, rhs)

let meet_avail a b =
  ExprKeyMap.merge
    (fun _ va vb ->
      match (va, vb) with
      | Some a, Some b when a = b -> Some a
      | _ -> None)
    a b

let kill_global_loads globals avail =
  ExprKeyMap.filter
    (fun key _ ->
      match key with
      | KeyLoad place -> not (PlaceSet.mem place globals)
      | KeyUn _ | KeyBin _ -> true)
    avail

let transfer_gvn_instr globals avail instr =
  match simplify_simple_instr instr with
  | Tcg.Move _ as instr -> (instr, avail)
  | Tcg.Un (dst, op, src) as instr -> (
      let key = KeyUn (op, src) in
      match ExprKeyMap.find_opt key avail with
      | Some value -> (Tcg.Move (dst, value), avail)
      | None -> (instr, ExprKeyMap.add key (Tcg.Temp dst) avail))
  | Tcg.Bin (dst, op, lhs, rhs) -> (
      let lhs, rhs = normalize_bin_operands op lhs rhs in
      let key = KeyBin (op, lhs, rhs) in
      match ExprKeyMap.find_opt key avail with
      | Some value -> (Tcg.Move (dst, value), avail)
      | None -> (Tcg.Bin (dst, op, lhs, rhs), ExprKeyMap.add key (Tcg.Temp dst) avail))
  | Tcg.Load (dst, place) as instr -> (
      let key = KeyLoad place in
      match ExprKeyMap.find_opt key avail with
      | Some value -> (Tcg.Move (dst, value), avail)
      | None -> (instr, ExprKeyMap.add key (Tcg.Temp dst) avail))
  | Tcg.Store (place, value) as instr ->
      let avail = ExprKeyMap.remove (KeyLoad place) avail in
      (instr, ExprKeyMap.add (KeyLoad place) value avail)
  | Tcg.Call _ as instr -> (instr, kill_global_loads globals avail)

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

let equal_avail_map = ExprKeyMap.equal ( = )

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

let kill_global_facts globals state =
  PlaceSet.fold (fun place acc -> set_place_fact acc place CpNac) globals state

let initial_cp_state global_init (f : Cfg.func) =
  let places =
    List.fold_left
      (fun places (param : Tcg.var) -> PlaceMap.add (Tcg.Local param.id) CpNac places)
      global_init f.params
  in
  { temps = IntMap.empty; places }

let transfer_simple_instr globals state instr =
  match instr with
  | Tcg.Move (dst, src) ->
      let src = rewrite_operand_const state src in
      let fact = eval_operand_fact state src in
      let instr = simplify_simple_instr (Tcg.Move (dst, src)) in
      (instr, set_temp_fact state dst fact)
  | Tcg.Un (dst, op, src) ->
      let src = rewrite_operand_const state src in
      let fact = fold_fact_un op (eval_operand_fact state src) in
      let instr = simplify_simple_instr (Tcg.Un (dst, op, src)) in
      (instr, set_temp_fact state dst fact)
  | Tcg.Bin (dst, op, lhs, rhs) ->
      let lhs = rewrite_operand_const state lhs in
      let rhs = rewrite_operand_const state rhs in
      let fact = fold_fact_bin op (eval_operand_fact state lhs) (eval_operand_fact state rhs) in
      let instr = simplify_simple_instr (Tcg.Bin (dst, op, lhs, rhs)) in
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
      let state = kill_global_facts globals state in
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

let run_transfer globals state (block : Cfg.block) =
  let body_rev, state =
    List.fold_left
      (fun (acc, state) instr ->
        let instr, state = transfer_simple_instr globals state instr in
        (instr :: acc, state))
      ([], state) block.body
  in
  let term, state = transfer_terminator state block.term in
  ({ block with body = List.rev body_rev; term; succs = Cfg.successors term }, state)

let compute_const_states global_init globals (f : Cfg.func) =
  let in_states = Hashtbl.create (List.length f.blocks) in
  let out_states = Hashtbl.create (List.length f.blocks) in
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
        let pred_states =
          List.filter_map (fun pred -> Hashtbl.find_opt out_states pred) block.preds
        in
        let in_state =
          if block.label = f.entry then meet_states (entry_state :: pred_states)
          else meet_states pred_states
        in
        let _, out_state = run_transfer globals in_state block in
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
          changed := true))
      f.blocks
  done;
  in_states

let const_propagate_func global_init globals (f : Cfg.func) =
  let in_states = compute_const_states global_init globals f in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let state =
          match Hashtbl.find_opt in_states block.label with
          | Some state -> state
          | None -> empty_cp_state
        in
        fst (run_transfer globals state block))
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

let run_gvn_transfer globals avail (block : Cfg.block) =
  let body_rev, avail =
    List.fold_left
      (fun (acc, avail) instr ->
        let instr, avail = transfer_gvn_instr globals avail instr in
        (instr :: acc, avail))
      ([], avail) block.body
  in
  ({ block with body = List.rev body_rev }, avail)

let compute_available_maps globals (f : Cfg.func) =
  let in_maps = Hashtbl.create (List.length f.blocks) in
  let out_maps = Hashtbl.create (List.length f.blocks) in
  let find_map table label =
    match Hashtbl.find_opt table label with
    | Some map -> map
    | None -> empty_avail
  in
  let meet_preds preds =
    match preds with
    | [] -> empty_avail
    | pred :: rest ->
        List.fold_left
          (fun acc pred -> meet_avail acc (find_map out_maps pred))
          (find_map out_maps pred) rest
  in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (block : Cfg.block) ->
        let in_avail = meet_preds block.preds in
        let _, out_avail = run_gvn_transfer globals in_avail block in
        let prev_in = find_map in_maps block.label in
        let prev_out = find_map out_maps block.label in
        if not (equal_avail_map in_avail prev_in) then (
          Hashtbl.replace in_maps block.label in_avail;
          changed := true);
        if not (equal_avail_map out_avail prev_out) then (
          Hashtbl.replace out_maps block.label out_avail;
          changed := true))
      f.blocks
  done;
  in_maps

let gvn_func globals (f : Cfg.func) =
  let in_maps = compute_available_maps globals f in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let avail =
          match Hashtbl.find_opt in_maps block.label with
          | Some avail -> avail
          | None -> empty_avail
        in
        fst (run_gvn_transfer globals avail block))
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

let copy_propagate_func (f : Cfg.func) =
  let copies = Hashtbl.create (max 8 f.temp_count) in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (function
          | Tcg.Move (dst, src) -> Hashtbl.replace copies dst src
          | _ -> ())
        block.body)
    f.blocks;
  let memo = Hashtbl.create (max 8 f.temp_count) in
  let rec resolve_operand seen = function
    | Tcg.Imm _ as operand -> operand
    | Tcg.Temp temp -> (
        if IntSet.mem temp seen then Tcg.Temp temp
        else
          match Hashtbl.find_opt memo temp with
          | Some operand -> operand
          | None ->
              let operand =
                match Hashtbl.find_opt copies temp with
                | Some src -> resolve_operand (IntSet.add temp seen) src
                | None -> Tcg.Temp temp
              in
              Hashtbl.replace memo temp operand;
              operand)
  in
  let rewrite_instr = function
    | Tcg.Move (dst, src) -> simplify_simple_instr (Tcg.Move (dst, resolve_operand IntSet.empty src))
    | Tcg.Un (dst, op, src) ->
        simplify_simple_instr (Tcg.Un (dst, op, resolve_operand IntSet.empty src))
    | Tcg.Bin (dst, op, lhs, rhs) ->
        simplify_simple_instr
          (Tcg.Bin
             ( dst,
               op,
               resolve_operand IntSet.empty lhs,
               resolve_operand IntSet.empty rhs ))
    | Tcg.Load _ as instr -> instr
    | Tcg.Store (place, value) ->
        Tcg.Store (place, resolve_operand IntSet.empty value)
    | Tcg.Call (dst, callee, args) ->
        Tcg.Call (dst, callee, List.map (resolve_operand IntSet.empty) args)
  in
  let rewrite_term (term : Cfg.terminator) =
    match term with
    | Cfg.Jump _ as term -> term
    | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
        let cond = resolve_operand IntSet.empty cond in
        if if_zero = if_nonzero then Cfg.Jump if_zero
        else (
          match cond with
          | Tcg.Imm value -> Cfg.Jump (if value = 0L then if_zero else if_nonzero)
          | _ -> Cfg.BranchZero (cond, if_zero, if_nonzero))
    | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
        let cond = resolve_operand IntSet.empty cond in
        if if_zero = if_nonzero then Cfg.Jump if_zero
        else (
          match cond with
          | Tcg.Imm value -> Cfg.Jump (if value <> 0L then if_nonzero else if_zero)
          | _ -> Cfg.BranchNonZero (cond, if_nonzero, if_zero))
    | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
        let lhs = resolve_operand IntSet.empty lhs in
        let rhs = resolve_operand IntSet.empty rhs in
        if if_true = if_false then Cfg.Jump if_true
        else (
          match (lhs, rhs) with
          | Tcg.Imm a, Tcg.Imm b -> (
              match fold_binop op a b with
              | Some value -> Cfg.Jump (if truth value then if_true else if_false)
              | None -> Cfg.BranchCompare (op, lhs, rhs, if_true, if_false))
          | _ -> Cfg.BranchCompare (op, lhs, rhs, if_true, if_false))
    | Cfg.Return None -> Cfg.Return None
    | Cfg.Return (Some value) -> Cfg.Return (Some (resolve_operand IntSet.empty value))
  in
  let blocks =
    List.map
      (fun (block : Cfg.block) ->
        let body = List.map rewrite_instr block.body in
        let term = rewrite_term block.term in
        { block with body; term; succs = Cfg.successors term })
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

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

let scan_simple_instr globals instr live_t live_p =
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
      let live_p = PlaceSet.union (local_places live_p) globals in
      (Some (Tcg.Call (kept_dst, callee, args)), live_t, live_p)

let scan_terminator globals (term : Cfg.terminator) live_t live_p =
  match term with
  | Cfg.Jump _ -> (term, live_t, live_p)
  | Cfg.BranchZero (cond, _, _) ->
      (term, add_operand_temps live_t cond, live_p)
  | Cfg.BranchNonZero (cond, _, _) ->
      (term, add_operand_temps live_t cond, live_p)
  | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
      (term, add_operand_temps (add_operand_temps live_t lhs) rhs, live_p)
  | Cfg.Return None -> (term, live_t, PlaceSet.union live_p globals)
  | Cfg.Return (Some value) ->
      ( term,
        add_operand_temps live_t value,
        PlaceSet.union live_p globals )

let scan_block globals (block : Cfg.block) live_t_out live_p_out =
  let term, live_t, live_p = scan_terminator globals block.term live_t_out live_p_out in
  let body_rev, live_t, live_p =
    List.fold_left
      (fun (acc, live_t, live_p) instr ->
        let kept, live_t, live_p = scan_simple_instr globals instr live_t live_p in
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

let compute_liveness globals (f : Cfg.func) =
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
        let _, live_t_in, live_p_in = scan_block globals block live_t_out live_p_out in
        if not (IntSet.equal live_t_in (table_find_or_empty live_in_t block.label IntSet.empty)) then (
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

let collect_local_ids (f : Cfg.func) =
  List.fold_left
    (fun acc (var : Tcg.var) -> IntSet.add var.id acc)
    IntSet.empty (f.params @ f.locals)

let first_some values =
  let rec loop = function
    | [] -> None
    | Some value :: _ -> Some value
    | None :: rest -> loop rest
  in
  loop values

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

let defs_temp = function
  | Tcg.Move (dst, _)
  | Tcg.Un (dst, _, _)
  | Tcg.Bin (dst, _, _, _)
  | Tcg.Load (dst, _) ->
      Some dst
  | Tcg.Store _ | Tcg.Call (None, _, _) -> None
  | Tcg.Call (Some dst, _, _) -> Some dst

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

let mem2reg_func (f : Cfg.func) =
  let all_candidates = collect_local_ids f in
  let rec attempt candidates =
    if IntSet.is_empty candidates then f
    else begin
      let next_temp = ref f.temp_count in
      let fresh_temp () =
        let temp = !next_temp in
        incr next_temp;
        temp
      in
      let seed_env, seed_instrs_rev =
        List.fold_left
          (fun (env, instrs_rev) (param : Tcg.var) ->
            if IntSet.mem param.id candidates then
              let temp = fresh_temp () in
              ( IntMap.add param.id (Tcg.Temp temp) env,
                Tcg.Load (temp, Tcg.Local param.id) :: instrs_rev )
            else (env, instrs_rev))
          (IntMap.empty, []) f.params
      in
      let seed_instrs = List.rev seed_instrs_rev in
      let in_envs = Hashtbl.create (List.length f.blocks) in
      let out_envs = Hashtbl.create (List.length f.blocks) in
      let phi_temps = Hashtbl.create (max 8 (List.length f.blocks)) in
      let get_env table label = table_find_or_empty table label IntMap.empty in
      let get_phi_temp label local_id =
        match Hashtbl.find_opt phi_temps (label, local_id) with
        | Some temp -> temp
        | None ->
            let temp = fresh_temp () in
            Hashtbl.add phi_temps (label, local_id) temp;
            temp
      in
      let compute_in_env (block : Cfg.block) =
        if block.label = f.entry then seed_env
        else
          IntSet.fold
            (fun local_id env ->
              let incoming =
                List.map (fun pred -> IntMap.find_opt local_id (get_env out_envs pred)) block.preds
              in
              let keep_value =
                match block.preds with
                | [] -> None
                | _ ->
                  match all_present incoming with
                  | Some values -> (
                      match all_same_operand values with
                      | Some value -> Some value
                      | None -> Some (Tcg.Temp (get_phi_temp block.label local_id)))
                  | None -> None
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
      let changed = ref true in
      while !changed do
        changed := false;
        List.iter
          (fun (block : Cfg.block) ->
            let in_env = compute_in_env block in
            let out_env = transfer_env in_env block in
            if not (equal_operand_map in_env (get_env in_envs block.label)) then (
              Hashtbl.replace in_envs block.label in_env;
              changed := true);
            if not (equal_operand_map out_env (get_env out_envs block.label)) then (
              Hashtbl.replace out_envs block.label out_env;
              changed := true))
          f.blocks
      done;
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
        f.blocks;
      if not (IntSet.is_empty !failed) then attempt (IntSet.diff candidates !failed)
      else
        let rewrite_block (block : Cfg.block) =
          let rec rewrite env acc = function
            | [] -> List.rev acc
            | instr :: rest -> (
                match instr with
                | Tcg.Load (dst, Tcg.Local id) when IntSet.mem id candidates -> (
                    match IntMap.find_opt id env with
                    | Some value ->
                        rewrite env (simplify_simple_instr (Tcg.Move (dst, value)) :: acc) rest
                    | None -> rewrite env (instr :: acc) rest)
                | Tcg.Store (Tcg.Local id, value) when IntSet.mem id candidates ->
                    rewrite (IntMap.add id value env) acc rest
                | _ -> rewrite env (instr :: acc) rest)
          in
          let body =
            (if block.label = f.entry then seed_instrs else [])
            @ rewrite (get_env in_envs block.label) [] block.body
          in
          { block with body }
        in
        let promoted_blocks = List.map rewrite_block f.blocks in
        let redirects = Hashtbl.create 16 in
        let edge_blocks_rev = ref [] in
        let edge_id = ref 0 in
        let fresh_edge_label () =
          let id = !edge_id in
          incr edge_id;
          Printf.sprintf ".L%s_mem2reg_edge_%d" f.label id
        in
        let build_parallel_copies copies =
          let snapshots = Hashtbl.create (List.length copies) in
          let snapshots_rev, assigns_rev =
            List.fold_left
              (fun (snapshots_rev, assigns_rev) (dst, src) ->
                if src = Tcg.Temp dst then (snapshots_rev, assigns_rev)
                else
                  match src with
                  | Tcg.Imm _ ->
                      (snapshots_rev, simplify_simple_instr (Tcg.Move (dst, src)) :: assigns_rev)
                  | Tcg.Temp src_temp ->
                      let snap_temp, snapshots_rev =
                        match Hashtbl.find_opt snapshots src_temp with
                        | Some temp -> (temp, snapshots_rev)
                        | None ->
                            let temp = fresh_temp () in
                            Hashtbl.add snapshots src_temp temp;
                            ( temp,
                              simplify_simple_instr (Tcg.Move (temp, Tcg.Temp src_temp))
                              :: snapshots_rev )
                      in
                      ( snapshots_rev,
                        simplify_simple_instr (Tcg.Move (dst, Tcg.Temp snap_temp)) :: assigns_rev ))
              ([], []) copies
          in
          List.rev snapshots_rev @ List.rev assigns_rev
        in
        List.iter
          (fun (succ_block : Cfg.block) ->
            let phi_copies =
              IntSet.fold
                (fun local_id acc ->
                  match Hashtbl.find_opt phi_temps (succ_block.label, local_id) with
                  | Some phi_temp -> (local_id, phi_temp) :: acc
                  | None -> acc)
                candidates []
            in
            if phi_copies <> [] then
              List.iter
                (fun pred ->
                  let pred_out = get_env out_envs pred in
                  let copies =
                    List.fold_left
                      (fun acc (local_id, phi_temp) ->
                        match IntMap.find_opt local_id pred_out with
                        | Some source when source <> Tcg.Temp phi_temp -> (phi_temp, source) :: acc
                        | Some _ | None -> acc)
                      [] phi_copies
                  in
                  match build_parallel_copies (List.rev copies) with
                  | [] -> ()
                  | body ->
                      let edge_label = fresh_edge_label () in
                      Hashtbl.add redirects (pred, succ_block.label) edge_label;
                      edge_blocks_rev :=
                        {
                          Cfg.label = edge_label;
                          body;
                          term = Cfg.Jump succ_block.label;
                          preds = [];
                          succs = [ succ_block.label ];
                        }
                        :: !edge_blocks_rev)
                succ_block.preds)
          promoted_blocks;
        let blocks =
          List.map
            (fun (block : Cfg.block) ->
              let term = redirect_successors block.label redirects block.term in
              { block with term; succs = Cfg.successors term })
            promoted_blocks
          @ List.rev !edge_blocks_rev
        in
        Cfg.rebuild_edges { f with temp_count = !next_temp; blocks }
    end
  in
  attempt all_candidates

let compute_dominators (f : Cfg.func) =
  let all_labels =
    List.fold_left (fun acc (block : Cfg.block) -> LabelSet.add block.label acc) LabelSet.empty
      f.blocks
  in
  let doms = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : Cfg.block) ->
      Hashtbl.add doms block.label (if block.label = f.entry then LabelSet.singleton block.label else all_labels))
    f.blocks;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (block : Cfg.block) ->
        if block.label <> f.entry then
          let pred_doms =
            List.map (fun pred -> table_find_or_empty doms pred all_labels) block.preds
          in
          let merged =
            match pred_doms with
            | [] -> all_labels
            | first :: rest -> List.fold_left LabelSet.inter first rest
          in
          let next_dom = LabelSet.add block.label merged in
          if not (LabelSet.equal next_dom (table_find_or_empty doms block.label LabelSet.empty)) then (
            Hashtbl.replace doms block.label next_dom;
            changed := true))
      f.blocks
  done;
  doms

let temp_def_blocks (f : Cfg.func) =
  let defs = Hashtbl.create (max 8 f.temp_count) in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (fun instr ->
          match defs_temp instr with
          | Some temp -> Hashtbl.replace defs temp block.label
          | None -> ())
        block.body)
    f.blocks;
  defs

let licm_candidate_info = function
  | Tcg.Move (dst, src) -> Some (dst, [ src ])
  | Tcg.Un (dst, _, src) -> Some (dst, [ src ])
  | Tcg.Bin (dst, _, lhs, rhs) -> Some (dst, [ lhs; rhs ])
  | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> None

let operand_invariant loop def_blocks ready_temps = function
  | Tcg.Imm _ -> true
  | Tcg.Temp temp -> (
      match Hashtbl.find_opt def_blocks temp with
      | Some def_label -> (not (LabelSet.mem def_label loop)) || IntSet.mem temp ready_temps
      | None -> true)

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

let licm_func (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.add block_map block.label block) f.blocks;
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
  if backedges = [] then f
  else
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
    let def_blocks = temp_def_blocks f in
    let current_blocks = Hashtbl.create (List.length f.blocks + List.length headers) in
    List.iter (fun (block : Cfg.block) -> Hashtbl.add current_blocks block.label block) f.blocks;
    let get_block label =
      match Hashtbl.find_opt current_blocks label with
      | Some block -> block
      | None -> failwith ("internal missing block: " ^ label)
    in
    let update_block (block : Cfg.block) =
      Hashtbl.replace current_blocks block.Cfg.label block
    in
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
        let header_block =
          match Hashtbl.find_opt block_map header with
          | Some block -> block
          | None -> get_block header
        in
        let outside_preds =
          List.filter (fun pred -> not (LabelSet.mem pred loop)) header_block.preds
        in
        if outside_preds <> [] then begin
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
                        match licm_candidate_info instr with
                        | Some (dst, operands)
                          when
                            List.for_all
                              (operand_invariant loop def_blocks !invariant_temps)
                              operands
                          ->
                            invariant_keys := InstrKeySet.add key !invariant_keys;
                            invariant_temps := IntSet.add dst !invariant_temps;
                            changed := true
                        | _ -> ())
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
                          match licm_candidate_info instr with
                          | Some (dst, operands)
                            when
                              List.for_all
                                (operand_invariant loop def_blocks !ready_temps)
                                operands
                            ->
                              hoisted_rev := instr :: !hoisted_rev;
                              scheduled_keys := InstrKeySet.add key !scheduled_keys;
                              ready_temps := IntSet.add dst !ready_temps;
                              progress := true
                          | _ -> ())
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
              update_block { preheader with body = preheader.body @ hoisted };
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

let fold_branch_tails_func (f : Cfg.func) =
  let globals = globals_in_func f in
  let live_in_t, _ = compute_liveness globals f in
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

let eliminate_dead_code_func (f : Cfg.func) =
  let globals = globals_in_func f in
  let live_in_t, live_in_p = compute_liveness globals f in
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
        let block, _, _ = scan_block globals block live_t_out live_p_out in
        { block with succs = Cfg.successors block.term })
      f.blocks
  in
  Cfg.rebuild_edges { f with blocks }

let optimize_func global_init globals (f : Cfg.func) =
  let promoted = mem2reg_func f in
  let step func =
    func
    |> const_propagate_func global_init globals
    |> copy_propagate_func
    |> gvn_func globals
    |> copy_propagate_func
    |> eliminate_dead_code_func
    |> licm_func
    |> const_propagate_func global_init globals
    |> copy_propagate_func
    |> gvn_func globals
    |> eliminate_dead_code_func
    |> fold_branch_tails_func
    |> thread_and_prune_func
  in
  let rec loop fuel current =
    if fuel = 0 then current
    else
      let next = step current in
      if next = current then current else loop (fuel - 1) next
  in
  loop 8 promoted

let optimize_cfg (analysis : Semant.analysis) (cfg : Cfg.program) =
  let global_init, globals =
    List.fold_left
      (fun (init, set) (g : Semant.global_decl) ->
        let place = Tcg.Global g.label in
        (PlaceMap.add place (CpConst g.init) init, PlaceSet.add place set))
      (PlaceMap.empty, PlaceSet.empty) analysis.globals
  in
  { Cfg.funcs = List.map (optimize_func global_init globals) cfg.funcs }
