open Ast

exception Error of string

module StringMap = Map.Make (String)
module IntSet = Set.Make (Int)
module LabelSet = Set.Make (String)

type layout = {
  local_offsets : (int, int) Hashtbl.t;
  temp_homes : (int, temp_home) Hashtbl.t;
  global_base_regs : (string, string) Hashtbl.t;
  frame_size : int;
  outgoing_area : int;
  saved_regs : string list;
}

and temp_home =
  | TempStack of int
  | TempReg of string

type ctx = {
  buf : Buffer.t;
  local_offsets : (int, int) Hashtbl.t;
  temp_homes : (int, temp_home) Hashtbl.t;
  global_base_regs : (string, string) Hashtbl.t;
  blocks_by_label : (string, Cfg.block) Hashtbl.t;
  live_out_temps : (string, IntSet.t) Hashtbl.t;
  epilogue : string;
}

let global_addr_reg = "t3"
let allocatable_temp_regs = [ "t4"; "t5"; "t6" ]
let allocatable_arg_regs = [ "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" ]
let allocatable_caller_regs = allocatable_temp_regs @ allocatable_arg_regs
let allocatable_saved_regs = [ "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11" ]
let reserved_global_base_regs = [ "s10"; "s11" ]

let align16 n = ((n + 15) / 16) * 16

let emit ctx s =
  Buffer.add_string ctx.buf s;
  Buffer.add_char ctx.buf '\n'

let emitf ctx fmt = Printf.ksprintf (emit ctx) fmt

let lookup_offset table id kind =
  match Hashtbl.find_opt table id with
  | Some off -> off
  | None -> raise (Error ("internal missing " ^ kind ^ " slot"))

let lookup_temp_home table temp =
  match Hashtbl.find_opt table temp with
  | Some home -> home
  | None -> raise (Error "internal missing temp home")

let lookup_block table label = Hashtbl.find_opt table label

let table_find_or_empty table key empty =
  match Hashtbl.find_opt table key with
  | Some value -> value
  | None -> empty

let reachable_labels entry blocks =
  let block_map = Hashtbl.create (List.length blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.add block_map block.label block) blocks;
  let rec visit work seen =
    match work with
    | [] -> seen
    | label :: rest ->
        if LabelSet.mem label seen then visit rest seen
        else
          let seen = LabelSet.add label seen in
          match Hashtbl.find_opt block_map label with
          | Some (block : Cfg.block) -> visit (List.rev_append block.succs rest) seen
          | None -> visit rest seen
  in
  visit [ entry ] LabelSet.empty

let compute_dominators (f : Cfg.func) =
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
          if not (LabelSet.equal next_dom (table_find_or_empty doms block.label LabelSet.empty))
          then (
            Hashtbl.replace doms block.label next_dom;
            changed := true))
      reachable_blocks
  done;
  doms

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

let contains_substring text needle =
  let text_len = String.length text in
  let needle_len = String.length needle in
  let rec loop i =
    if i + needle_len > text_len then false
    else if String.sub text i needle_len = needle then true
    else loop (i + 1)
  in
  needle_len = 0 || loop 0

let is_mem2reg_edge_label label = contains_substring label "_mem2reg_edge_"
let is_gprom_edge_label label = contains_substring label "_gprom_edge_"
let is_licm_preheader_label label = contains_substring label "_licm_preheader_"
let is_split_preheader_label label = contains_substring label "_split_preheader_"
let is_split_summary_label label = contains_substring label "_split_summary_"
let is_counted_loop_label label = contains_substring label "_counted_loop_"

let is_edge_anchor_label label = is_mem2reg_edge_label label || is_gprom_edge_label label

let is_before_successor_anchor_label label =
  is_licm_preheader_label label
  || is_split_preheader_label label
  || is_split_summary_label label
  || is_counted_loop_label label

let is_synthetic_label label = is_edge_anchor_label label || is_before_successor_anchor_label label

let build_block_anchor_maps blocks =
  let before_map = Hashtbl.create 8 in
  let after_map = Hashtbl.create 8 in
  let append_anchor table key block =
    let blocks =
      match Hashtbl.find_opt table key with
      | Some blocks -> blocks @ [ block ]
      | None -> [ block ]
    in
    Hashtbl.replace table key blocks
  in
  List.iter
    (fun (block : Cfg.block) ->
      if is_edge_anchor_label block.label then
        match block.preds with
        | pred :: _ -> append_anchor after_map pred block
        | [] -> ()
      else if is_before_successor_anchor_label block.label then
        match block.succs with
        | succ :: _ -> append_anchor before_map succ block
        | [] -> ())
    blocks;
  (before_map, after_map)

let max_call_args (f : Cfg.func) =
  List.fold_left
    (fun current (block : Cfg.block) ->
      List.fold_left
        (fun acc instr ->
          match instr with
          | Tcg.Call (_, _, args) -> max acc (List.length args)
          | _ -> acc)
        current block.body)
    0 f.blocks

let referenced_local_ids (f : Cfg.func) =
  let add_place locals = function
    | Tcg.Local id -> IntSet.add id locals
    | Tcg.Global _ -> locals
  in
  List.fold_left
    (fun locals (block : Cfg.block) ->
      List.fold_left
        (fun locals instr ->
          match instr with
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Call _ -> locals
          | Tcg.Load (_, place) -> add_place locals place
          | Tcg.Store (place, _) -> add_place locals place)
        locals block.body)
    IntSet.empty f.blocks

let add_operand_temp live = function
  | Tcg.Temp temp -> IntSet.add temp live
  | Tcg.Imm _ -> live

let scan_term_live_in (term : Cfg.terminator) live_out =
  match term with
  | Cfg.Jump _ | Cfg.Return None -> live_out
  | Cfg.BranchZero (cond, _, _)
  | Cfg.BranchNonZero (cond, _, _)
  | Cfg.Return (Some cond) ->
      add_operand_temp live_out cond
  | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
      add_operand_temp (add_operand_temp live_out lhs) rhs

let scan_simple_live_in instr live =
  match instr with
  | Tcg.Move (dst, src)
  | Tcg.Un (dst, _, src) ->
      add_operand_temp (IntSet.remove dst live) src
  | Tcg.Bin (dst, _, lhs, rhs) ->
      add_operand_temp (add_operand_temp (IntSet.remove dst live) lhs) rhs
  | Tcg.Load (dst, _) -> IntSet.remove dst live
  | Tcg.Store (_, value) -> add_operand_temp live value
  | Tcg.Call (dst, _, args) ->
      let live =
        match dst with
        | Some temp -> IntSet.remove temp live
        | None -> live
      in
      List.fold_left add_operand_temp live args

let compute_temp_live_sets (f : Cfg.func) =
  let live_in = Hashtbl.create (List.length f.blocks) in
  let blocks = List.rev f.blocks in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (block : Cfg.block) ->
        let live_out =
          List.fold_left
            (fun acc succ ->
              IntSet.union acc (table_find_or_empty live_in succ IntSet.empty))
            IntSet.empty block.succs
        in
        let live_in_block =
          List.fold_left
            (fun live instr -> scan_simple_live_in instr live)
            (scan_term_live_in block.term live_out)
            (List.rev block.body)
        in
        if not (IntSet.equal live_in_block (table_find_or_empty live_in block.label IntSet.empty)) then (
          Hashtbl.replace live_in block.label live_in_block;
          changed := true))
      blocks
  done;
  let live_out = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : Cfg.block) ->
      let block_live_out =
        List.fold_left
          (fun acc succ ->
            IntSet.union acc (table_find_or_empty live_in succ IntSet.empty))
          IntSet.empty block.succs
      in
      Hashtbl.replace live_out block.label block_live_out)
    f.blocks;
  (live_in, live_out)

let defs_temp = function
  | Tcg.Move (dst, _)
  | Tcg.Un (dst, _, _)
  | Tcg.Bin (dst, _, _, _)
  | Tcg.Load (dst, _) ->
      Some dst
  | Tcg.Store _ | Tcg.Call (None, _, _) -> None
  | Tcg.Call (Some dst, _, _) -> Some dst

type interval = {
  temp : int;
  start_pos : int;
  end_pos : int;
  use_count : int;
  def_count : int;
  loop_use_score : int;
  loop_def_score : int;
  loop_carried_score : int;
  defined_by_call : bool;
  max_call_arg_index : int option;
  used_in_call_args : bool;
  used_as_late_arg : bool;
  call_crossings : int;
  spill_weight : int;
  hint_temps : (int * int) list;
}

type temp_stats = {
  mutable start_pos : int;
  mutable end_pos : int;
  mutable use_count : int;
  mutable def_count : int;
  mutable loop_use_score : int;
  mutable loop_def_score : int;
  mutable loop_carried_score : int;
  mutable defined_by_call : bool;
  mutable max_call_arg_index : int option;
  mutable used_in_call_args : bool;
  mutable used_as_late_arg : bool;
}

type active_entry = {
  interval : interval;
  reg : string;
}

let note_move_hint hint_tables temp hinted =
  let temp_hints =
    match Hashtbl.find_opt hint_tables temp with
    | Some hints -> hints
    | None ->
        let hints = Hashtbl.create 4 in
        Hashtbl.add hint_tables temp hints;
        hints
  in
  let count = Option.value ~default:0 (Hashtbl.find_opt temp_hints hinted) in
  Hashtbl.replace temp_hints hinted (count + 1)

let get_temp_stats stats_table temp pos =
  match Hashtbl.find_opt stats_table temp with
  | Some stats ->
      stats.start_pos <- min stats.start_pos pos;
      stats.end_pos <- max stats.end_pos pos;
      stats
  | None ->
      let stats =
        {
          start_pos = pos;
          end_pos = pos;
          use_count = 0;
          def_count = 0;
          loop_use_score = 0;
          loop_def_score = 0;
          loop_carried_score = 0;
          defined_by_call = false;
          max_call_arg_index = None;
          used_in_call_args = false;
          used_as_late_arg = false;
        }
      in
      Hashtbl.add stats_table temp stats;
      stats

let note_temp_use stats_table temp pos loop_depth =
  let stats = get_temp_stats stats_table temp pos in
  stats.use_count <- stats.use_count + 1;
  stats.loop_use_score <- stats.loop_use_score + loop_depth

let note_temp_def stats_table temp pos loop_depth =
  let stats = get_temp_stats stats_table temp pos in
  stats.def_count <- stats.def_count + 1;
  stats.loop_def_score <- stats.loop_def_score + loop_depth

let spill_weight
    use_count
    def_count
    loop_use_score
    loop_def_score
    loop_carried_score
    call_crossings
    start_pos
    end_pos
  =
  let benefit =
    max 1
      ((4 * use_count)
      + (2 * def_count)
      + (8 * loop_use_score)
      + (4 * loop_def_score)
      + (48 * loop_carried_score)
      + (12 * call_crossings))
  in
  let span = max 1 (end_pos - start_pos + 1) in
  (benefit * 1024) / span

let fits_simm12 n = n >= -2048L && n <= 2047L

let compute_loop_depths (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.add block_map block.label block) f.blocks;
  let doms = compute_dominators f in
  let depths = Hashtbl.create (List.length f.blocks) in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (fun succ ->
          if LabelSet.mem succ (table_find_or_empty doms block.label LabelSet.empty) then
            let loop = natural_loop block_map succ block.label in
            LabelSet.iter
              (fun label ->
                let depth = Option.value ~default:0 (Hashtbl.find_opt depths label) in
                Hashtbl.replace depths label (depth + 1))
              loop)
        block.succs)
    f.blocks;
  depths

let schedule_primary_blocks (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.add block_map block.label block) f.blocks;
  let reachable = reachable_labels f.entry f.blocks in
  let loop_depths = compute_loop_depths f in
  let original_order = Hashtbl.create (List.length f.blocks) in
  List.iteri (fun index (block : Cfg.block) -> Hashtbl.add original_order block.label index) f.blocks;
  let primary_blocks =
    List.filter
      (fun (block : Cfg.block) ->
        LabelSet.mem block.label reachable && not (is_synthetic_label block.label))
      f.blocks
  in
  let primary_labels =
    List.fold_left
      (fun labels (block : Cfg.block) -> LabelSet.add block.label labels)
      LabelSet.empty primary_blocks
  in
  let loop_depth label = Option.value ~default:0 (Hashtbl.find_opt loop_depths label) in
  let original_index label =
    Option.value ~default:max_int (Hashtbl.find_opt original_order label)
  in
  let rec resolve_primary_successor seen label =
    if LabelSet.mem label seen || not (LabelSet.mem label reachable) then None
    else if LabelSet.mem label primary_labels then Some label
    else
      match Hashtbl.find_opt block_map label with
      | Some (block : Cfg.block) when is_synthetic_label label -> (
          match block.succs with
          | [ next_label ] -> resolve_primary_successor (LabelSet.add label seen) next_label
          | _ -> None)
      | Some _ | None -> None
  in
  let block_heat (block : Cfg.block) =
    (4096 * loop_depth block.label)
    + (64 * min 4 (List.length block.preds))
    + (8 * min 8 (List.length block.body))
  in
  let edge_heat (block : Cfg.block) succ_label =
    let succ_block : Cfg.block = Hashtbl.find block_map succ_label in
    let current_depth = loop_depth block.label in
    let succ_depth = loop_depth succ_label in
    let depth_bonus =
      if succ_depth < current_depth then -8192 * (current_depth - succ_depth)
      else 2048 * (succ_depth - current_depth)
    in
    let jump_bonus =
      match block.term with
      | Cfg.Jump target when target = succ_label -> 16384
      | _ -> 0
    in
    let chain_bonus = if List.length succ_block.preds <= 1 then 1024 else 0 in
    jump_bonus + depth_bonus + (256 * succ_depth) + chain_bonus - original_index succ_label
  in
  let visited = Hashtbl.create (List.length primary_blocks) in
  let ordered_rev = ref [] in
  let rec follow_trace label =
    if not (Hashtbl.mem visited label) then begin
      Hashtbl.add visited label ();
      ordered_rev := Hashtbl.find block_map label :: !ordered_rev;
      let block : Cfg.block = Hashtbl.find block_map label in
      let successors =
        List.fold_left
          (fun acc succ ->
            match resolve_primary_successor LabelSet.empty succ with
            | Some resolved
              when not (Hashtbl.mem visited resolved)
                   && not (List.exists (fun existing -> existing = resolved) acc) ->
                resolved :: acc
            | Some _ | None -> acc)
          [] block.succs
        |> List.rev
        |> List.sort (fun a b ->
               match compare (edge_heat block b) (edge_heat block a) with
               | 0 -> compare (original_index a) (original_index b)
               | c -> c)
      in
      match successors with
      | next_label :: _ -> follow_trace next_label
      | [] -> ()
    end
  in
  let initial_start = resolve_primary_successor LabelSet.empty f.entry in
  Option.iter follow_trace initial_start;
  let remaining_starts =
    List.sort
      (fun (a : Cfg.block) (b : Cfg.block) ->
        match compare (block_heat b) (block_heat a) with
        | 0 -> compare (original_index a.label) (original_index b.label)
        | c -> c)
      primary_blocks
  in
  List.iter (fun (block : Cfg.block) -> follow_trace block.label) remaining_starts;
  List.rev !ordered_rev

let schedule_func_blocks_with_hot_traces (f : Cfg.func) =
  let before_map, after_map = build_block_anchor_maps f.blocks in
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.add block_map block.label block) f.blocks;
  let primary_order = schedule_primary_blocks f in
  let emitted = Hashtbl.create (List.length f.blocks) in
  let ordered_rev = ref [] in
  let rec emit_block (block : Cfg.block) =
    if not (Hashtbl.mem emitted block.label) then begin
      Hashtbl.add emitted block.label ();
      List.iter emit_block (table_find_or_empty before_map block.label []);
      ordered_rev := block :: !ordered_rev;
      List.iter emit_block (table_find_or_empty after_map block.label [])
    end
  in
  Option.iter emit_block (Hashtbl.find_opt block_map f.entry);
  List.iter emit_block primary_order;
  List.iter emit_block f.blocks;
  { f with blocks = List.rev !ordered_rev }

type global_access_stats = {
  mutable count : int;
  mutable score : int;
}

let compute_global_access_stats (f : Cfg.func) =
  let loop_depths = compute_loop_depths f in
  let stats = Hashtbl.create 8 in
  let note_global label loop_depth =
    let entry =
      match Hashtbl.find_opt stats label with
      | Some entry -> entry
      | None ->
          let entry = { count = 0; score = 0 } in
          Hashtbl.add stats label entry;
          entry
    in
    entry.count <- entry.count + 1;
    entry.score <- entry.score + 1 + (4 * loop_depth)
  in
  List.iter
    (fun (block : Cfg.block) ->
      let loop_depth = Option.value ~default:0 (Hashtbl.find_opt loop_depths block.label) in
      List.iter
        (function
          | Tcg.Load (_, Tcg.Global label)
          | Tcg.Store (Tcg.Global label, _) ->
              note_global label loop_depth
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Load _ | Tcg.Store _ | Tcg.Call _ -> ())
        block.body)
    f.blocks;
  stats

let select_global_base_regs (f : Cfg.func) =
  let stats = compute_global_access_stats f in
  let candidates =
    Hashtbl.fold
      (fun label ({ count; score } : global_access_stats) acc ->
        if count >= 2 && score >= 6 then (label, score, count) :: acc else acc)
      stats []
    |> List.sort (fun (a_label, a_score, a_count) (b_label, b_score, b_count) ->
           match compare b_score a_score with
           | 0 -> (
               match compare b_count a_count with
               | 0 -> compare a_label b_label
               | c -> c)
           | c -> c)
  in
  let mapping = Hashtbl.create (List.length reserved_global_base_regs) in
  let rec assign regs remaining =
    match (regs, remaining) with
    | reg :: regs_rest, (label, _, _) :: rest ->
        Hashtbl.add mapping label reg;
        assign regs_rest rest
    | _ -> ()
  in
  assign reserved_global_base_regs candidates;
  mapping

let compute_temp_intervals (f : Cfg.func) =
  let live_in, live_out = compute_temp_live_sets f in
  let stats_table = Hashtbl.create (max 8 f.temp_count) in
  let hint_tables = Hashtbl.create (max 8 f.temp_count) in
  let block_ranges = Hashtbl.create (List.length f.blocks) in
  let loop_depths = compute_loop_depths f in
  let call_sites_rev = ref [] in
  let note_operand pos loop_depth = function
    | Tcg.Temp temp -> note_temp_use stats_table temp pos loop_depth
    | Tcg.Imm _ -> ()
  in
  let note_instr pos loop_depth = function
    | Tcg.Move (dst, src) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        note_temp_def stats_table dst def_pos loop_depth;
        note_operand use_pos loop_depth src;
        (match src with
        | Tcg.Temp src_temp ->
            note_move_hint hint_tables dst src_temp;
            note_move_hint hint_tables src_temp dst
        | Tcg.Imm _ -> ())
    | Tcg.Un (dst, _, src) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        note_temp_def stats_table dst def_pos loop_depth;
        note_operand use_pos loop_depth src
    | Tcg.Bin (dst, _, lhs, rhs) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        note_temp_def stats_table dst def_pos loop_depth;
        note_operand use_pos loop_depth lhs;
        note_operand use_pos loop_depth rhs
    | Tcg.Load (dst, _) ->
        let def_pos = (2 * pos) + 1 in
        note_temp_def stats_table dst def_pos loop_depth
    | Tcg.Store (_, value) ->
        note_operand (2 * pos) loop_depth value
    | Tcg.Call (dst, _, args) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        call_sites_rev := def_pos :: !call_sites_rev;
        Option.iter
          (fun temp ->
            note_temp_def stats_table temp def_pos loop_depth;
            let stats = get_temp_stats stats_table temp def_pos in
            stats.defined_by_call <- true)
          dst;
        List.iteri
          (fun i arg ->
            match arg with
            | Tcg.Temp temp ->
                note_temp_use stats_table temp use_pos loop_depth;
                let stats = get_temp_stats stats_table temp use_pos in
                stats.used_in_call_args <- true;
                stats.max_call_arg_index <-
                  Some
                    (match stats.max_call_arg_index with
                    | Some prev -> max prev i
                    | None -> i);
                if i > 0 then stats.used_as_late_arg <- true
            | Tcg.Imm _ -> ())
          args
  in
  let note_term pos loop_depth = function
    | Cfg.Jump _ | Cfg.Return None -> ()
    | Cfg.BranchZero (cond, _, _)
    | Cfg.BranchNonZero (cond, _, _)
    | Cfg.Return (Some cond) ->
        note_operand (2 * pos) loop_depth cond
    | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
        let use_pos = 2 * pos in
        note_operand use_pos loop_depth lhs;
        note_operand use_pos loop_depth rhs
  in
  let pos = ref 0 in
  List.iter
    (fun (block : Cfg.block) ->
      let loop_depth = Option.value ~default:0 (Hashtbl.find_opt loop_depths block.label) in
      let block_start = 2 * !pos in
      List.iter
        (fun instr ->
          note_instr !pos loop_depth instr;
          incr pos)
        block.body;
      note_term !pos loop_depth block.term;
      incr pos;
      Hashtbl.replace block_ranges block.label (block_start, (2 * !pos) - 1))
    f.blocks;
  let doms = compute_dominators f in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (fun succ ->
          if LabelSet.mem succ (table_find_or_empty doms block.label LabelSet.empty) then
            let carried =
              IntSet.inter
                (table_find_or_empty live_out block.label IntSet.empty)
                (table_find_or_empty live_in succ IntSet.empty)
            in
            let loop_depth = Option.value ~default:1 (Hashtbl.find_opt loop_depths succ) in
            IntSet.iter
              (fun temp ->
                match Hashtbl.find_opt stats_table temp with
                | Some stats -> stats.loop_carried_score <- stats.loop_carried_score + loop_depth
                | None -> ())
              carried)
        block.succs)
    f.blocks;
  List.iter
    (fun (block : Cfg.block) ->
      match Hashtbl.find_opt block_ranges block.label with
      | None -> ()
      | Some (block_start, block_end) ->
          let live =
            IntSet.union
              (table_find_or_empty live_in block.label IntSet.empty)
              (table_find_or_empty live_out block.label IntSet.empty)
          in
          IntSet.iter
            (fun temp ->
              let stats = get_temp_stats stats_table temp block_start in
              stats.start_pos <- min stats.start_pos block_start;
              stats.end_pos <- max stats.end_pos block_end)
            live)
    f.blocks;
  Hashtbl.fold
    (fun temp (stats : temp_stats) acc ->
      let hint_temps =
        match Hashtbl.find_opt hint_tables temp with
        | Some hints ->
            Hashtbl.fold (fun hinted count acc -> (hinted, count) :: acc) hints []
            |> List.sort (fun (a_temp, a_count) (b_temp, b_count) ->
                   match compare b_count a_count with
                   | 0 -> compare a_temp b_temp
                   | c -> c)
        | None -> []
      in
      let call_crossings =
        List.fold_left
          (fun acc call_pos ->
            if stats.start_pos < call_pos && call_pos < stats.end_pos then acc + 1 else acc)
          0 !call_sites_rev
      in
      {
        temp;
        start_pos = stats.start_pos;
        end_pos = stats.end_pos;
        use_count = stats.use_count;
        def_count = stats.def_count;
        loop_use_score = stats.loop_use_score;
        loop_def_score = stats.loop_def_score;
        loop_carried_score = stats.loop_carried_score;
        defined_by_call = stats.defined_by_call;
        max_call_arg_index = stats.max_call_arg_index;
        used_in_call_args = stats.used_in_call_args;
        used_as_late_arg = stats.used_as_late_arg;
        call_crossings;
        spill_weight =
          spill_weight
            stats.use_count
            stats.def_count
            stats.loop_use_score
            stats.loop_def_score
            stats.loop_carried_score
            call_crossings
            stats.start_pos
            stats.end_pos;
        hint_temps;
      }
      :: acc)
    stats_table []
  |> List.sort (fun (a : interval) (b : interval) ->
         match compare a.start_pos b.start_pos with
         | 0 -> compare a.temp b.temp
         | c -> c)

let allocate_temp_regs ?(reserved_saved_regs = []) (f : Cfg.func) =
  let intervals = compute_temp_intervals f in
  let homes = Hashtbl.create (max 8 f.temp_count) in
  let active = ref [] in
  let temp_saved_regs =
    List.filter (fun reg -> not (List.mem reg reserved_saved_regs)) allocatable_saved_regs
  in
  let free_regs = ref (allocatable_caller_regs @ temp_saved_regs) in
  let remove_reg reg regs =
    let rec loop acc = function
      | [] -> List.rev acc
      | current :: rest ->
          if current = reg then List.rev_append acc rest else loop (current :: acc) rest
    in
    loop [] regs
  in
  let interval_prefer_spill (a : interval) (b : interval) =
    match compare a.loop_carried_score b.loop_carried_score with
    | 0 -> (
        match compare (a.loop_use_score + a.loop_def_score) (b.loop_use_score + b.loop_def_score) with
        | 0 -> (
            match compare a.spill_weight b.spill_weight with
            | 0 -> (
                match compare a.use_count b.use_count with
                | 0 -> (
                    match compare b.end_pos a.end_pos with
                    | 0 -> b.temp < a.temp
                    | c -> c < 0)
                | c -> c < 0)
            | c -> c < 0)
        | c -> c < 0)
    | c -> c < 0
  in
  let arg_reg_index = function
    | "a0" -> Some 0
    | "a1" -> Some 1
    | "a2" -> Some 2
    | "a3" -> Some 3
    | "a4" -> Some 4
    | "a5" -> Some 5
    | "a6" -> Some 6
    | "a7" -> Some 7
    | _ -> None
  in
  let prefer_saved_regs (interval : interval) =
    interval.loop_carried_score >= 2
    && interval.loop_use_score + interval.loop_def_score >= 8
  in
  let allowed_arg_regs (interval : interval) =
    if interval.call_crossings <> 0 then []
    else
      let min_safe_index = Option.value ~default:0 interval.max_call_arg_index in
      List.filter
        (fun reg ->
          match arg_reg_index reg with
          | Some index -> index >= min_safe_index
          | None -> false)
        allocatable_arg_regs
  in
  let allowed_regs (interval : interval) =
    if interval.call_crossings = 0 then
      if prefer_saved_regs interval then
        temp_saved_regs @ allocatable_temp_regs @ allowed_arg_regs interval
      else allocatable_temp_regs @ allowed_arg_regs interval @ temp_saved_regs
    else temp_saved_regs
  in
  let allowed_free_regs interval =
    let allowed = allowed_regs interval in
    List.filter (fun reg -> List.mem reg !free_regs) allowed
  in
  let choose_free_reg (interval : interval) =
    let free_allowed_regs = allowed_free_regs interval in
    let hinted_regs = Hashtbl.create 4 in
    List.iter
      (fun (hint_temp, count) ->
        match Hashtbl.find_opt homes hint_temp with
        | Some (TempReg reg) when List.mem reg free_allowed_regs ->
            let total = Option.value ~default:0 (Hashtbl.find_opt hinted_regs reg) in
            Hashtbl.replace hinted_regs reg (total + count)
        | Some (TempReg _) | Some (TempStack _) | None -> ())
      interval.hint_temps;
    let preferred_call_reg =
      if interval.defined_by_call && List.mem "a0" free_allowed_regs then Some "a0" else None
    in
    let preferred =
      match preferred_call_reg with
      | Some reg -> Some (reg, max_int)
      | None ->
          Hashtbl.fold
            (fun reg count best ->
              match best with
              | None -> Some (reg, count)
              | Some (best_reg, best_count) ->
                  if count > best_count || (count = best_count && reg < best_reg) then
                    Some (reg, count)
                  else best)
            hinted_regs None
    in
    match preferred with
    | Some (reg, _) ->
        free_regs := remove_reg reg !free_regs;
        reg
    | None -> (
        match free_allowed_regs with
        | reg :: _ ->
            free_regs := remove_reg reg !free_regs;
            reg
        | [] -> failwith "internal missing free register")
  in
  let insert_active (interval : interval) reg =
    let rec loop acc = function
      | [] -> List.rev ({ interval; reg } :: acc)
      | (({ interval = other; _ } as entry) :: rest) ->
          if interval.end_pos < other.end_pos then
            List.rev_append acc ({ interval; reg } :: entry :: rest)
          else loop (entry :: acc) rest
    in
    active := loop [] !active
  in
  let expire current_start =
    let rec loop kept released = function
      | [] ->
          active := List.rev kept;
          free_regs := List.sort compare (released @ !free_regs)
      | ({ interval; reg } as entry) :: rest ->
          if interval.end_pos < current_start then loop kept (reg :: released) rest
          else loop (entry :: kept) released rest
    in
    loop [] [] !active
  in
  List.iter
    (fun (interval : interval) ->
      expire interval.start_pos;
      if allowed_free_regs interval <> [] then (
        let reg = choose_free_reg interval in
        Hashtbl.replace homes interval.temp (TempReg reg);
        insert_active interval reg)
      else
        let allowed = allowed_regs interval in
        let spill_candidates = List.filter (fun entry -> List.mem entry.reg allowed) !active in
        match spill_candidates with
        | [] -> ()
        | first :: rest ->
            let spill_entry =
              List.fold_left
                (fun best entry ->
                  if interval_prefer_spill entry.interval best.interval then entry else best)
                first rest
            in
            if interval_prefer_spill interval spill_entry.interval then ()
            else begin
              active :=
                List.filter (fun entry -> entry.interval.temp <> spill_entry.interval.temp) !active;
              Hashtbl.remove homes spill_entry.interval.temp;
              Hashtbl.replace homes interval.temp (TempReg spill_entry.reg);
              insert_active interval spill_entry.reg
            end)
    intervals;
  let saved_regs =
    Hashtbl.fold
      (fun _ home acc ->
        match home with
        | TempReg reg when List.mem reg allocatable_saved_regs ->
            if List.mem reg acc then acc else reg :: acc
        | TempReg _ -> acc
        | TempStack _ -> acc)
      homes []
    |> List.sort compare
  in
  (homes, saved_regs)

let compute_layout (f : Cfg.func) =
  let local_offsets = Hashtbl.create 64 in
  let global_base_regs = select_global_base_regs f in
  let reserved_saved_regs =
    Hashtbl.fold
      (fun _ reg acc -> if List.mem reg acc then acc else reg :: acc)
      global_base_regs []
    |> List.sort compare
  in
  let temp_homes, temp_saved_regs = allocate_temp_regs ~reserved_saved_regs f in
  let saved_regs =
    List.fold_left
      (fun acc reg -> if List.mem reg acc then acc else reg :: acc)
      temp_saved_regs reserved_saved_regs
    |> List.sort compare
  in
  let referenced_locals = referenced_local_ids f in
  let save_area_size = 4 * (2 + List.length saved_regs) in
  let next = ref (save_area_size + 4) in
  let alloc_slot () =
    let off = - !next in
    next := !next + 4;
    off
  in
  let alloc_local (var : Tcg.var) =
    if IntSet.mem var.id referenced_locals && not (Hashtbl.mem local_offsets var.id) then
      Hashtbl.add local_offsets var.id (alloc_slot ())
  in
  List.iter alloc_local f.params;
  List.iter alloc_local f.locals;
  for temp = 0 to f.temp_count - 1 do
    if not (Hashtbl.mem temp_homes temp) then Hashtbl.add temp_homes temp (TempStack (alloc_slot ()))
  done;
  let extra_args = max 0 (max_call_args f - 8) in
  let outgoing_area = align16 (extra_args * 4) in
  let frame_bytes = outgoing_area + (!next - 4) in
  {
    local_offsets;
    temp_homes;
    global_base_regs;
    frame_size = align16 frame_bytes;
    outgoing_area;
    saved_regs;
  }

let emit_reg_copy ctx dst src =
  if dst <> src then emitf ctx "    addi %s, %s, 0" dst src

let load_operand ctx dst = function
  | Tcg.Imm n -> emitf ctx "    li %s, %Ld" dst n
  | Tcg.Temp temp -> (
      match lookup_temp_home ctx.temp_homes temp with
      | TempStack off -> emitf ctx "    lw %s, %d(s0)" dst off
      | TempReg reg -> emit_reg_copy ctx dst reg)

let operand_reg ctx scratch operand =
  match operand with
  | Tcg.Temp temp -> (
      match lookup_temp_home ctx.temp_homes temp with
      | TempReg reg -> reg
      | TempStack _ ->
          load_operand ctx scratch operand;
          scratch)
  | Tcg.Imm _ ->
      load_operand ctx scratch operand;
      scratch

let store_temp ctx temp src =
  match lookup_temp_home ctx.temp_homes temp with
  | TempStack off -> emitf ctx "    sw %s, %d(s0)" src off
  | TempReg reg -> emit_reg_copy ctx reg src

let cached_global_base_reg ctx label = Hashtbl.find_opt ctx.global_base_regs label

let load_place ctx dst = function
  | Tcg.Local id ->
      emitf ctx "    lw %s, %d(s0)" dst (lookup_offset ctx.local_offsets id "local")
  | Tcg.Global label -> (
      match cached_global_base_reg ctx label with
      | Some base_reg -> emitf ctx "    lw %s, 0(%s)" dst base_reg
      | None ->
          emitf ctx "    la %s, %s" global_addr_reg label;
          emitf ctx "    lw %s, 0(%s)" dst global_addr_reg)

let store_place ctx src = function
  | Tcg.Local id ->
      emitf ctx "    sw %s, %d(s0)" src (lookup_offset ctx.local_offsets id "local")
  | Tcg.Global label -> (
      match cached_global_base_reg ctx label with
      | Some base_reg -> emitf ctx "    sw %s, 0(%s)" src base_reg
      | None ->
          emitf ctx "    la %s, %s" global_addr_reg label;
          emitf ctx "    sw %s, 0(%s)" src global_addr_reg)

let emit_unop ctx op dst src =
  match op with
  | UPlus -> emit_reg_copy ctx dst src
  | UMinus -> emitf ctx "    neg %s, %s" dst src
  | UNot -> emitf ctx "    sltiu %s, %s, 1" dst src

let emit_binop ctx op dst lhs rhs =
  match op with
  | Add -> emitf ctx "    add %s, %s, %s" dst lhs rhs
  | Sub -> emitf ctx "    sub %s, %s, %s" dst lhs rhs
  | Mul -> emitf ctx "    mul %s, %s, %s" dst lhs rhs
  | Div -> emitf ctx "    div %s, %s, %s" dst lhs rhs
  | Mod -> emitf ctx "    rem %s, %s, %s" dst lhs rhs
  | Lt -> emitf ctx "    slt %s, %s, %s" dst lhs rhs
  | Gt -> emitf ctx "    slt %s, %s, %s" dst rhs lhs
  | Le ->
      emitf ctx "    slt %s, %s, %s" dst rhs lhs;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Ge ->
      emitf ctx "    slt %s, %s, %s" dst lhs rhs;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Eq ->
      emitf ctx "    sub %s, %s, %s" dst lhs rhs;
      emitf ctx "    sltiu %s, %s, 1" dst dst
  | Ne ->
      emitf ctx "    sub %s, %s, %s" dst lhs rhs;
      emitf ctx "    sltu %s, x0, %s" dst dst
  | LAnd | LOr -> raise (Error "logical operators should not reach binary lowering")

let emit_compare_zero ctx op dst reg zero_on_left =
  match (op, zero_on_left) with
  | Eq, _ -> emitf ctx "    sltiu %s, %s, 1" dst reg
  | Ne, _ -> emitf ctx "    sltu %s, x0, %s" dst reg
  | Lt, false
  | Gt, true ->
      emitf ctx "    slt %s, %s, x0" dst reg
  | Lt, true
  | Gt, false ->
      emitf ctx "    slt %s, x0, %s" dst reg
  | Le, false
  | Ge, true ->
      emitf ctx "    slt %s, x0, %s" dst reg;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Le, true
  | Ge, false ->
      emitf ctx "    slt %s, %s, x0" dst reg;
      emitf ctx "    xori %s, %s, 1" dst dst
  | Add, _
  | Sub, _
  | Mul, _
  | Div, _
  | Mod, _
  | LAnd, _
  | LOr, _ ->
      raise (Error "non-compare op in compare-zero lowering")

let emit_binop_operands ctx op dst lhs rhs =
  match (op, lhs, rhs) with
  | Add, Tcg.Imm imm, rhs when fits_simm12 imm ->
      let rhs_reg = operand_reg ctx "t0" rhs in
      emitf ctx "    addi %s, %s, %Ld" dst rhs_reg imm
  | Add, rhs, Tcg.Imm imm when fits_simm12 imm ->
      let rhs_reg = operand_reg ctx "t0" rhs in
      emitf ctx "    addi %s, %s, %Ld" dst rhs_reg imm
  | Sub, lhs, Tcg.Imm imm when fits_simm12 Int64.(neg imm) ->
      let lhs_reg = operand_reg ctx "t0" lhs in
      emitf ctx "    addi %s, %s, %Ld" dst lhs_reg Int64.(neg imm)
  | Eq, Tcg.Imm 0L, rhs
  | Ne, Tcg.Imm 0L, rhs
  | Lt, Tcg.Imm 0L, rhs
  | Gt, Tcg.Imm 0L, rhs
  | Le, Tcg.Imm 0L, rhs
  | Ge, Tcg.Imm 0L, rhs ->
      let rhs_reg = operand_reg ctx "t0" rhs in
      emit_compare_zero ctx op dst rhs_reg true
  | Eq, lhs, Tcg.Imm 0L
  | Ne, lhs, Tcg.Imm 0L
  | Lt, lhs, Tcg.Imm 0L
  | Gt, lhs, Tcg.Imm 0L
  | Le, lhs, Tcg.Imm 0L
  | Ge, lhs, Tcg.Imm 0L ->
      let lhs_reg = operand_reg ctx "t0" lhs in
      emit_compare_zero ctx op dst lhs_reg false
  | _ ->
       let lhs_reg = operand_reg ctx "t0" lhs in
       let rhs_reg = operand_reg ctx "t1" rhs in
       emit_binop ctx op dst lhs_reg rhs_reg

let emit_call_args ctx args =
  List.iteri
    (fun i arg ->
      if i < 8 then load_operand ctx (Printf.sprintf "a%d" i) arg
      else (
        let arg_reg = operand_reg ctx "t0" arg in
        emitf ctx "    sw %s, %d(sp)" arg_reg ((i - 8) * 4)))
    args

let emit_call ctx callee args =
  emit_call_args ctx args;
  emitf ctx "    call %s" callee

let temp_live_out ctx label temp =
  IntSet.mem temp (table_find_or_empty ctx.live_out_temps label IntSet.empty)

let replace_temp_operand dst replacement = function
  | Tcg.Temp temp when temp = dst -> replacement
  | operand -> operand

let gen_simple_instr ctx = function
  | Tcg.Move (dst, src) ->
      begin
        match lookup_temp_home ctx.temp_homes dst with
        | TempReg reg -> load_operand ctx reg src
        | TempStack off -> (
            match src with
            | Tcg.Temp temp -> (
                match lookup_temp_home ctx.temp_homes temp with
                | TempReg reg -> emitf ctx "    sw %s, %d(s0)" reg off
                | TempStack _ ->
                    load_operand ctx "t0" src;
                    emitf ctx "    sw t0, %d(s0)" off)
            | Tcg.Imm _ ->
                load_operand ctx "t0" src;
                emitf ctx "    sw t0, %d(s0)" off)
      end
  | Tcg.Un (dst, op, src) ->
      let src_reg = operand_reg ctx "t0" src in
      begin
        match lookup_temp_home ctx.temp_homes dst with
        | TempReg reg -> emit_unop ctx op reg src_reg
        | TempStack off ->
            emit_unop ctx op "t2" src_reg;
            emitf ctx "    sw t2, %d(s0)" off
      end
  | Tcg.Bin (dst, op, lhs, rhs) ->
      begin
        match lookup_temp_home ctx.temp_homes dst with
        | TempReg reg -> emit_binop_operands ctx op reg lhs rhs
        | TempStack off ->
            emit_binop_operands ctx op "t2" lhs rhs;
            emitf ctx "    sw t2, %d(s0)" off
      end
  | Tcg.Load (dst, place) ->
      begin
        match lookup_temp_home ctx.temp_homes dst with
        | TempReg reg -> load_place ctx reg place
        | TempStack _ ->
            load_place ctx "t0" place;
            store_temp ctx dst "t0"
      end
  | Tcg.Store (place, value) ->
      let value_reg = operand_reg ctx "t0" value in
      store_place ctx value_reg place
  | Tcg.Call (dst, callee, args) ->
      emit_call ctx callee args;
      Option.iter (fun temp -> store_temp ctx temp "a0") dst

let emit_jump_if_needed ctx next_label target =
  if next_label <> Some target then emitf ctx "    j %s" target

let emit_branch_result ctx reg if_true if_false next_label =
  if next_label = Some if_false then emitf ctx "    bnez %s, %s" reg if_true
  else if next_label = Some if_true then emitf ctx "    beqz %s, %s" reg if_false
  else (
    emitf ctx "    bnez %s, %s" reg if_true;
    emitf ctx "    j %s" if_false)

let compare_operand_reg ctx scratch = function
  | Tcg.Imm 0L -> "x0"
  | operand -> operand_reg ctx scratch operand

let emit_binary_branch ctx opcode inverse lhs rhs if_true if_false next_label =
  if next_label = Some if_false then emitf ctx "    %s %s, %s, %s" opcode lhs rhs if_true
  else if next_label = Some if_true then emitf ctx "    %s %s, %s, %s" inverse lhs rhs if_false
  else (
    emitf ctx "    %s %s, %s, %s" opcode lhs rhs if_true;
    emitf ctx "    j %s" if_false)

let emit_compare_branch ctx op lhs rhs if_true if_false next_label =
  let direct_zero_branch reg is_equal =
    if is_equal then emit_branch_result ctx reg if_false if_true next_label
    else emit_branch_result ctx reg if_true if_false next_label
  in
  match (op, lhs, rhs) with
  | Eq, lhs, rhs when lhs = rhs -> emit_jump_if_needed ctx next_label if_true
  | Ne, lhs, rhs when lhs = rhs -> emit_jump_if_needed ctx next_label if_false
  | Lt, lhs, rhs when lhs = rhs -> emit_jump_if_needed ctx next_label if_false
  | Gt, lhs, rhs when lhs = rhs -> emit_jump_if_needed ctx next_label if_false
  | Le, lhs, rhs when lhs = rhs -> emit_jump_if_needed ctx next_label if_true
  | Ge, lhs, rhs when lhs = rhs -> emit_jump_if_needed ctx next_label if_true
  | Eq, Tcg.Imm 0L, rhs ->
      let reg = operand_reg ctx "t0" rhs in
      direct_zero_branch reg true
  | Eq, rhs, Tcg.Imm 0L ->
      let reg = operand_reg ctx "t0" rhs in
      direct_zero_branch reg true
  | Ne, Tcg.Imm 0L, rhs ->
      let reg = operand_reg ctx "t0" rhs in
      direct_zero_branch reg false
  | Ne, rhs, Tcg.Imm 0L ->
      let reg = operand_reg ctx "t0" rhs in
      direct_zero_branch reg false
  | Eq, Tcg.Imm imm, rhs when fits_simm12 Int64.(neg imm) ->
      let reg = operand_reg ctx "t0" rhs in
      emitf ctx "    addi t2, %s, %Ld" reg Int64.(neg imm);
      direct_zero_branch "t2" true
  | Eq, rhs, Tcg.Imm imm when fits_simm12 Int64.(neg imm) ->
      let reg = operand_reg ctx "t0" rhs in
      emitf ctx "    addi t2, %s, %Ld" reg Int64.(neg imm);
      direct_zero_branch "t2" true
  | Ne, Tcg.Imm imm, rhs when fits_simm12 Int64.(neg imm) ->
      let reg = operand_reg ctx "t0" rhs in
      emitf ctx "    addi t2, %s, %Ld" reg Int64.(neg imm);
      direct_zero_branch "t2" false
  | Ne, rhs, Tcg.Imm imm when fits_simm12 Int64.(neg imm) ->
      let reg = operand_reg ctx "t0" rhs in
      emitf ctx "    addi t2, %s, %Ld" reg Int64.(neg imm);
      direct_zero_branch "t2" false
  | Eq, lhs, rhs ->
      let lhs_reg = compare_operand_reg ctx "t0" lhs in
      let rhs_reg = compare_operand_reg ctx "t1" rhs in
      emit_binary_branch ctx "beq" "bne" lhs_reg rhs_reg if_true if_false next_label
  | Ne, lhs, rhs ->
      let lhs_reg = compare_operand_reg ctx "t0" lhs in
      let rhs_reg = compare_operand_reg ctx "t1" rhs in
      emit_binary_branch ctx "bne" "beq" lhs_reg rhs_reg if_true if_false next_label
  | Lt, lhs, Tcg.Imm 0L ->
      let lhs_reg = operand_reg ctx "t0" lhs in
      emit_binary_branch ctx "blt" "bge" lhs_reg "x0" if_true if_false next_label
  | Gt, Tcg.Imm 0L, rhs ->
      let rhs_reg = operand_reg ctx "t0" rhs in
      emit_binary_branch ctx "blt" "bge" rhs_reg "x0" if_true if_false next_label
  | Gt, lhs, Tcg.Imm 0L ->
      let lhs_reg = operand_reg ctx "t0" lhs in
      emit_binary_branch ctx "blt" "bge" "x0" lhs_reg if_true if_false next_label
  | Lt, Tcg.Imm 0L, rhs ->
      let rhs_reg = operand_reg ctx "t0" rhs in
      emit_binary_branch ctx "blt" "bge" "x0" rhs_reg if_true if_false next_label
  | Le, lhs, Tcg.Imm 0L ->
      let lhs_reg = operand_reg ctx "t0" lhs in
      emit_binary_branch ctx "bge" "blt" "x0" lhs_reg if_true if_false next_label
  | Ge, Tcg.Imm 0L, rhs ->
      let rhs_reg = operand_reg ctx "t0" rhs in
      emit_binary_branch ctx "bge" "blt" "x0" rhs_reg if_true if_false next_label
  | Ge, lhs, Tcg.Imm 0L ->
      let lhs_reg = operand_reg ctx "t0" lhs in
      emit_binary_branch ctx "bge" "blt" lhs_reg "x0" if_true if_false next_label
  | Le, Tcg.Imm 0L, rhs ->
      let rhs_reg = operand_reg ctx "t0" rhs in
      emit_binary_branch ctx "bge" "blt" rhs_reg "x0" if_true if_false next_label
  | Lt, lhs, rhs ->
      let lhs_reg = compare_operand_reg ctx "t0" lhs in
      let rhs_reg = compare_operand_reg ctx "t1" rhs in
      emit_binary_branch ctx "blt" "bge" lhs_reg rhs_reg if_true if_false next_label
  | Gt, lhs, rhs ->
      let lhs_reg = compare_operand_reg ctx "t0" lhs in
      let rhs_reg = compare_operand_reg ctx "t1" rhs in
      emit_binary_branch ctx "blt" "bge" rhs_reg lhs_reg if_true if_false next_label
  | Le, lhs, rhs ->
      let lhs_reg = compare_operand_reg ctx "t0" lhs in
      let rhs_reg = compare_operand_reg ctx "t1" rhs in
      emit_binary_branch ctx "bge" "blt" rhs_reg lhs_reg if_true if_false next_label
  | Ge, lhs, rhs ->
      let lhs_reg = compare_operand_reg ctx "t0" lhs in
      let rhs_reg = compare_operand_reg ctx "t1" rhs in
      emit_binary_branch ctx "bge" "blt" lhs_reg rhs_reg if_true if_false next_label
  | Add, _, _
  | Sub, _, _
  | Mul, _, _
  | Div, _, _
  | Mod, _, _
  | LAnd, _, _
  | LOr, _, _ ->
      raise (Error "non-compare op in compare-branch lowering")

let gen_terminator ctx next_label = function
  | Cfg.Jump label -> emit_jump_if_needed ctx next_label label
  | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
      let cond_reg = operand_reg ctx "t0" cond in
      emit_branch_result ctx cond_reg if_nonzero if_zero next_label
  | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
      let cond_reg = operand_reg ctx "t0" cond in
      emit_branch_result ctx cond_reg if_nonzero if_zero next_label
  | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
      emit_compare_branch ctx op lhs rhs if_true if_false next_label
  | Cfg.Return None -> emitf ctx "    j %s" ctx.epilogue
  | Cfg.Return (Some value) ->
      load_operand ctx "a0" value;
      emitf ctx "    j %s" ctx.epilogue

let forwarded_move_jump_terminator ctx dst src succ_label =
  if temp_live_out ctx succ_label dst then None
  else
    match lookup_block ctx.blocks_by_label succ_label with
  | Some ({ body = []; term; _ } : Cfg.block) -> (
      match term with
      | Cfg.Return (Some value) ->
          let value' = replace_temp_operand dst src value in
          if value' <> value then Some (Cfg.Return (Some value')) else None
      | Cfg.BranchZero (cond, if_zero, if_nonzero) ->
          let cond' = replace_temp_operand dst src cond in
          if cond' <> cond then Some (Cfg.BranchZero (cond', if_zero, if_nonzero)) else None
      | Cfg.BranchNonZero (cond, if_nonzero, if_zero) ->
          let cond' = replace_temp_operand dst src cond in
          if cond' <> cond then Some (Cfg.BranchNonZero (cond', if_nonzero, if_zero)) else None
      | Cfg.BranchCompare (op, lhs, rhs, if_true, if_false) ->
          let lhs' = replace_temp_operand dst src lhs in
          let rhs' = replace_temp_operand dst src rhs in
          if lhs' <> lhs || rhs' <> rhs then
            Some (Cfg.BranchCompare (op, lhs', rhs', if_true, if_false))
          else None
      | Cfg.Jump _ | Cfg.Return None -> None)
  | Some _ | None -> None

let gen_tail_return_instr ctx (instr : Tcg.simple_instr) =
  match instr with
  | Tcg.Move (_, src) ->
      load_operand ctx "a0" src;
      emitf ctx "    j %s" ctx.epilogue
  | Tcg.Un (_, op, src) ->
      let src_reg = operand_reg ctx "t0" src in
      emit_unop ctx op "a0" src_reg;
      emitf ctx "    j %s" ctx.epilogue
  | Tcg.Bin (_, op, lhs, rhs) ->
      emit_binop_operands ctx op "a0" lhs rhs;
      emitf ctx "    j %s" ctx.epilogue
  | Tcg.Load (_, place) ->
      load_place ctx "a0" place;
      emitf ctx "    j %s" ctx.epilogue
  | Tcg.Store _ -> raise (Error "store cannot feed tail return directly")
  | Tcg.Call (_, callee, args) ->
      emit_call ctx callee args;
      emitf ctx "    j %s" ctx.epilogue

let gen_tail_branch_instr ctx next_label (instr : Tcg.simple_instr) if_nonzero if_zero =
  match instr with
  | Tcg.Move (_, src) ->
      let reg = operand_reg ctx "t0" src in
      emit_branch_result ctx reg if_nonzero if_zero next_label
  | Tcg.Un (_, op, src) -> (
      let src_reg = operand_reg ctx "t0" src in
      match op with
      | UPlus | UMinus -> emit_branch_result ctx src_reg if_nonzero if_zero next_label
      | UNot -> emit_branch_result ctx src_reg if_zero if_nonzero next_label)
  | Tcg.Bin (_, op, lhs, rhs) -> (
      match op with
      | Eq | Ne | Lt | Gt | Le | Ge ->
          emit_compare_branch ctx op lhs rhs if_nonzero if_zero next_label
      | Add | Sub | Mul | Div | Mod ->
          emit_binop_operands ctx op "t2" lhs rhs;
          emit_branch_result ctx "t2" if_nonzero if_zero next_label
      | LAnd | LOr ->
          raise (Error "logical operators should not reach tail branch lowering"))
  | Tcg.Load (_, place) ->
      load_place ctx "t0" place;
      emit_branch_result ctx "t0" if_nonzero if_zero next_label
  | Tcg.Store _ -> raise (Error "store cannot feed tail branch directly")
  | Tcg.Call (_, callee, args) ->
      emit_call ctx callee args;
      emit_branch_result ctx "a0" if_nonzero if_zero next_label

let gen_block ctx next_label (block : Cfg.block) =
  emitf ctx "%s:" block.label;
  match (List.rev block.body, block.term) with
  | (last_instr :: rev_prefix), Cfg.Return (Some (Tcg.Temp temp))
    when defs_temp last_instr = Some temp ->
      List.iter (gen_simple_instr ctx) (List.rev rev_prefix);
      gen_tail_return_instr ctx last_instr
  | (Tcg.Move (dst, src) :: rev_prefix), Cfg.Jump succ_label -> (
      match forwarded_move_jump_terminator ctx dst src succ_label with
      | Some term ->
          List.iter (gen_simple_instr ctx) (List.rev rev_prefix);
          gen_terminator ctx None term
      | None ->
          List.iter (gen_simple_instr ctx) block.body;
          gen_terminator ctx next_label block.term)
  | (last_instr :: rev_prefix), Cfg.BranchZero (Tcg.Temp temp, if_zero, if_nonzero)
    when defs_temp last_instr = Some temp && not (temp_live_out ctx block.label temp) ->
      List.iter (gen_simple_instr ctx) (List.rev rev_prefix);
      gen_tail_branch_instr ctx next_label last_instr if_nonzero if_zero
  | (last_instr :: rev_prefix), Cfg.BranchNonZero (Tcg.Temp temp, if_nonzero, if_zero)
    when defs_temp last_instr = Some temp && not (temp_live_out ctx block.label temp) ->
      List.iter (gen_simple_instr ctx) (List.rev rev_prefix);
      gen_tail_branch_instr ctx next_label last_instr if_nonzero if_zero
  | _ ->
      List.iter (gen_simple_instr ctx) block.body;
      gen_terminator ctx next_label block.term

let gen_func buf (f : Cfg.func) =
  let f = schedule_func_blocks_with_hot_traces f in
  let layout = compute_layout f in
  let epilogue = Printf.sprintf ".L_%s_epilogue" f.label in
  let blocks_by_label = Hashtbl.create (List.length f.blocks) in
  let _, live_out_temps = compute_temp_live_sets f in
  List.iter (fun (block : Cfg.block) -> Hashtbl.add blocks_by_label block.label block) f.blocks;
  let ctx =
    {
      buf;
      local_offsets = layout.local_offsets;
      temp_homes = layout.temp_homes;
      global_base_regs = layout.global_base_regs;
      blocks_by_label;
      live_out_temps;
      epilogue;
    }
  in
  emit ctx "    .text";
  emit ctx "    .align 2";
  if f.name = "main" then emit ctx "    .globl main";
  emitf ctx "%s:" f.label;
  emitf ctx "    addi sp, sp, -%d" layout.frame_size;
  emitf ctx "    sw ra, %d(sp)" (layout.frame_size - 4);
  emitf ctx "    sw s0, %d(sp)" (layout.frame_size - 8);
  List.iteri
    (fun i reg -> emitf ctx "    sw %s, %d(sp)" reg (layout.frame_size - (12 + (4 * i))))
    layout.saved_regs;
  emitf ctx "    addi s0, sp, %d" layout.frame_size;
  Hashtbl.fold (fun label reg acc -> (reg, label) :: acc) layout.global_base_regs []
  |> List.sort (fun (a_reg, a_label) (b_reg, b_label) ->
         match compare a_reg b_reg with
         | 0 -> compare a_label b_label
         | c -> c)
  |> List.iter (fun (reg, label) -> emitf ctx "    la %s, %s" reg label);
  List.iteri
    (fun i (param : Tcg.var) ->
      match Hashtbl.find_opt layout.local_offsets param.id with
      | None -> ()
      | Some off ->
          if i < 8 then emitf ctx "    sw a%d, %d(s0)" i off
          else (
            emitf ctx "    lw t0, %d(s0)" ((i - 8) * 4);
            emitf ctx "    sw t0, %d(s0)" off))
    f.params;
  let rec emit_blocks = function
    | [] -> ()
    | [ block ] -> gen_block ctx None block
    | block :: ((next_block :: _) as rest) ->
        gen_block ctx (Some next_block.label) block;
        emit_blocks rest
  in
  emit_blocks f.blocks;
  emitf ctx "%s:" epilogue;
  List.iteri
    (fun i reg -> emitf ctx "    lw %s, %d(sp)" reg (layout.frame_size - (12 + (4 * i))))
    layout.saved_regs;
  emitf ctx "    lw ra, %d(sp)" (layout.frame_size - 4);
  emitf ctx "    lw s0, %d(sp)" (layout.frame_size - 8);
  emitf ctx "    addi sp, sp, %d" layout.frame_size;
  emit ctx "    ret";
  emit ctx ""

let emit_global buf g =
  Buffer.add_string buf "    .data\n";
  Buffer.add_string buf "    .align 2\n";
  Buffer.add_string buf (g.Semant.label ^ ":\n");
  Buffer.add_string buf (Printf.sprintf "    .word %Ld\n\n" g.Semant.init)

let generate (analysis : Semant.analysis) (cfg : Cfg.program) =
  let buf = Buffer.create 16384 in
  Buffer.add_string buf "    .option nopic\n\n";
  List.iter (emit_global buf) analysis.globals;
  List.iter (gen_func buf) cfg.funcs;
  Buffer.contents buf
