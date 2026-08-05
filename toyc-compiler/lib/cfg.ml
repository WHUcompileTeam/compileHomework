type terminator =
  | Jump of Tcg.label
  | BranchZero of Tcg.operand * Tcg.label * Tcg.label
  | BranchNonZero of Tcg.operand * Tcg.label * Tcg.label
  | BranchCompare of Ast.binop * Tcg.operand * Tcg.operand * Tcg.label * Tcg.label
  | Return of Tcg.operand option

type block = {
  label : Tcg.label;
  body : Tcg.simple_instr list;
  term : terminator;
  preds : Tcg.label list;
  succs : Tcg.label list;
}

type func = {
  ret : Ast.typ;
  name : string;
  label : string;
  entry : Tcg.label;
  params : Tcg.var list;
  locals : Tcg.var list;
  temp_count : int;
  blocks : block list;
}

type program = {
  funcs : func list;
}

type raw_term =
  | RawJump of Tcg.label
  | RawBranchZero of Tcg.operand * Tcg.label
  | RawBranchNonZero of Tcg.operand * Tcg.label
  | RawReturn of Tcg.operand option

type raw_block = {
  label : Tcg.label;
  body : Tcg.simple_instr list;
  term : raw_term option;
}

let successors = function
  | Jump label -> [ label ]
  | BranchZero (_, if_zero, if_nonzero)
  | BranchNonZero (_, if_nonzero, if_zero)
  | BranchCompare (_, _, _, if_nonzero, if_zero) ->
      [ if_zero; if_nonzero ]
  | Return _ -> []

let make_block label body term =
  { label; body; term; preds = []; succs = successors term }

let add_pred table label pred =
  let preds =
    match Hashtbl.find_opt table label with
    | Some existing -> existing
    | None -> []
  in
  Hashtbl.replace table label (pred :: preds)

let rebuild_edges (f : func) =
  let pred_table = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : block) ->
      List.iter (fun succ -> add_pred pred_table succ block.label) block.succs)
    f.blocks;
  let blocks =
    List.map
      (fun (block : block) ->
        let preds =
          match Hashtbl.find_opt pred_table block.label with
          | Some labels -> List.rev labels
          | None -> []
        in
        { block with preds })
      f.blocks
  in
  { f with blocks }

let of_raw_blocks (meta : func) (raw_blocks : raw_block list) =
  let rec build acc = function
    | [] -> List.rev acc
    | [ (block : raw_block) ] ->
        let term =
          match block.term with
          | Some (RawJump label) -> Jump label
          | Some (RawBranchZero (op, target)) -> BranchZero (op, target, block.label)
          | Some (RawBranchNonZero (op, target)) ->
              BranchNonZero (op, target, block.label)
          | Some (RawReturn value) -> Return value
          | None -> Return None
        in
        build (make_block block.label block.body term :: acc) []
    | (block : raw_block) :: ((next_block :: _) as rest) ->
        let term =
          match block.term with
          | Some (RawJump label) -> Jump label
          | Some (RawBranchZero (op, target)) ->
              BranchZero (op, target, next_block.label)
          | Some (RawBranchNonZero (op, target)) ->
              BranchNonZero (op, target, next_block.label)
          | Some (RawReturn value) -> Return value
          | None -> Jump next_block.label
        in
        build (make_block block.label block.body term :: acc) rest
  in
  rebuild_edges { meta with blocks = build [] raw_blocks }

let lower_func (f : Tcg.func) =
  let synthetic_id = ref 0 in
  let fresh_dead_label () =
    let id = !synthetic_id in
    incr synthetic_id;
    Printf.sprintf ".L%s_dead_%d" f.label id
  in
  let blocks_rev = ref [] in
  let current_label = ref None in
  let current_body_rev = ref [] in
  let current_term = ref None in
  let close_block () =
    match !current_label with
    | None -> ()
    | Some label ->
        blocks_rev :=
          {
            label;
            body = List.rev !current_body_rev;
            term = !current_term;
          }
          :: !blocks_rev;
        current_label := None;
        current_body_rev := [];
        current_term := None
  in
  let start_block label =
    current_label := Some label;
    current_body_rev := [];
    current_term := None
  in
  let ensure_block () =
    match !current_label with
    | Some _ -> ()
    | None -> start_block (fresh_dead_label ())
  in
  let split_if_terminated () =
    match !current_term with
    | Some _ ->
        close_block ();
        start_block (fresh_dead_label ())
    | None -> ()
  in
  List.iter
    (function
      | Tcg.Label label -> (
          match !current_label with
          | None -> start_block label
          | Some _ ->
              close_block ();
              start_block label)
      | Tcg.Op op ->
          ensure_block ();
          split_if_terminated ();
          current_body_rev := op :: !current_body_rev
      | Tcg.Goto label ->
          ensure_block ();
          split_if_terminated ();
          current_term := Some (RawJump label)
      | Tcg.IfZero (op, label) ->
          ensure_block ();
          split_if_terminated ();
          current_term := Some (RawBranchZero (op, label))
      | Tcg.IfNonZero (op, label) ->
          ensure_block ();
          split_if_terminated ();
          current_term := Some (RawBranchNonZero (op, label))
      | Tcg.Return value ->
          ensure_block ();
          split_if_terminated ();
          current_term := Some (RawReturn value))
    f.body;
  close_block ();
  of_raw_blocks
    {
      ret = f.ret;
      name = f.name;
      label = f.label;
      entry = f.entry;
      params = f.params;
      locals = f.locals;
      temp_count = f.temp_count;
      blocks = [];
    }
    (List.rev !blocks_rev)

let of_tcg (tcg : Tcg.program) =
  { funcs = List.map lower_func tcg.funcs }
