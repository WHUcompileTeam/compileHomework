open Ast

exception Error of string

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)
module IntSet = Set.Make (Int)

type layout = {
  local_offsets : (int, int) Hashtbl.t;
  temp_homes : (int, temp_home) Hashtbl.t;
  direct_params : (int * int * int) list;
  global_regs : (string, string) Hashtbl.t;
  frame_size : int;
  outgoing_area : int;
  saved_regs : string list;
  uses_s0 : bool;
  saves_ra : bool;
}

and temp_home =
  | TempStack of int
  | TempReg of string

type ctx = {
  buf : Buffer.t;
  local_offsets : (int, int) Hashtbl.t;
  temp_homes : (int, temp_home) Hashtbl.t;
  global_regs : (string, string) Hashtbl.t;
  blocks_by_label : (string, Cfg.block) Hashtbl.t;
  live_out_temps : (string, IntSet.t) Hashtbl.t;
  epilogue : string;
  func : string;
  entry : string;
  params : Tcg.var list;
  direct_params : (int * int * int) list;
  frame_size : int;
  saved_regs : string list;
  uses_s0 : bool;
  saves_ra : bool;
}

let global_addr_reg = "t3"
let allocatable_temp_regs = [ "t4"; "t5"; "t6" ]
let allocatable_arg_regs = [ "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" ]
let allocatable_caller_regs = allocatable_temp_regs @ allocatable_arg_regs
let allocatable_saved_regs = [ "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11" ]
let allocatable_regs = allocatable_caller_regs @ allocatable_saved_regs

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
let is_licm_preheader_label label = contains_substring label "_licm_preheader_"
let is_synthetic_label label = is_mem2reg_edge_label label || is_licm_preheader_label label

let schedule_func_blocks (f : Cfg.func) =
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
      if is_mem2reg_edge_label block.label then
        match block.preds with
        | pred :: _ -> append_anchor after_map pred block
        | [] -> ()
      else if is_licm_preheader_label block.label then
        match block.succs with
        | succ :: _ -> append_anchor before_map succ block
        | [] -> ())
    f.blocks;
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
  Option.iter emit_block (List.find_opt (fun (block : Cfg.block) -> block.label = f.entry) f.blocks);
  List.iter
    (fun (block : Cfg.block) ->
      if block.label <> f.entry && not (is_synthetic_label block.label) then emit_block block)
    f.blocks;
  List.iter (fun (block : Cfg.block) -> if block.label <> f.entry then emit_block block) f.blocks;
  { f with blocks = List.rev !ordered_rev }

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

let is_call = function
  | Tcg.Call _ -> true
  | _ -> false

let needs_return_address (f : Cfg.func) =
  List.exists
    (fun (block : Cfg.block) ->
      match (List.rev block.body, block.term) with
      | (Tcg.Call (Some dst, _, args) :: rest), Cfg.Return (Some (Tcg.Temp result))
        when dst = result && List.length args <= 8 ->
          List.exists is_call rest
      | _ -> List.exists is_call block.body)
    f.blocks

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

let loop_global_labels (f : Cfg.func) =
  let block_map = Hashtbl.create (List.length f.blocks) in
  List.iter (fun (block : Cfg.block) -> Hashtbl.replace block_map block.label block) f.blocks;
  let loop_blocks = ref StringSet.empty in
  let collect_loop header tail =
    let rec walk seen = function
      | [] -> seen
      | label :: rest when StringSet.mem label seen -> walk seen rest
      | label :: rest ->
          let seen = StringSet.add label seen in
          let preds =
            match Hashtbl.find_opt block_map label with
            | Some (block : Cfg.block) when label <> header -> block.preds
            | Some _ | None -> []
          in
          walk seen (preds @ rest)
    in
    loop_blocks := StringSet.union !loop_blocks (walk (StringSet.singleton header) [ tail ])
  in
  let visited = ref StringSet.empty in
  let active = ref StringSet.empty in
  let rec visit label =
    if not (StringSet.mem label !visited) then begin
      visited := StringSet.add label !visited;
      active := StringSet.add label !active;
      (match Hashtbl.find_opt block_map label with
      | Some (block : Cfg.block) ->
          List.iter
            (fun succ ->
              if StringSet.mem succ !active then collect_loop succ label else visit succ)
            block.succs
      | None -> ());
      active := StringSet.remove label !active
    end
  in
  visit f.entry;
  List.fold_left
    (fun globals (block : Cfg.block) ->
      if StringSet.mem block.label !loop_blocks then
        List.fold_left
          (fun globals -> function
            | Tcg.Load (_, Tcg.Global label)
            | Tcg.Store (Tcg.Global label, _) ->
                StringSet.add label globals
            | _ -> globals)
          globals block.body
      else globals)
    StringSet.empty f.blocks

let find_direct_params (f : Cfg.func) =
  let reads = Hashtbl.create 8 in
  let written = Hashtbl.create 8 in
  let leading = Hashtbl.create 8 in
  List.iter
    (fun (block : Cfg.block) ->
      List.iter
        (function
          | Tcg.Load (temp, Tcg.Local id) ->
              let old = Option.value ~default:[] (Hashtbl.find_opt reads id) in
              Hashtbl.replace reads id ((block.label, temp) :: old)
          | Tcg.Store (Tcg.Local id, _) -> Hashtbl.replace written id ()
          | Tcg.Move _ | Tcg.Un _ | Tcg.Bin _ | Tcg.Call _
          | Tcg.Load (_, Tcg.Global _) | Tcg.Store (Tcg.Global _, _) -> ())
        block.body)
    f.blocks;
  Option.iter
    (fun (block : Cfg.block) ->
      let rec scan = function
        | Tcg.Load (temp, Tcg.Local id) :: rest ->
            Hashtbl.replace leading id temp;
            scan rest
        | _ -> ()
      in
      scan block.body)
    (List.find_opt (fun (block : Cfg.block) -> block.label = f.entry) f.blocks);
  List.mapi
    (fun index (param : Tcg.var) ->
      if index >= 8 || Hashtbl.mem written param.id then None
      else
        match Hashtbl.find_opt reads param.id with
        | Some [ (label, temp) ]
          when label = f.entry && Hashtbl.find_opt leading param.id = Some temp ->
            Some (param.id, temp, index)
        | Some _ | None -> None)
    f.params
  |> List.filter_map Fun.id

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
          defined_by_call = false;
          max_call_arg_index = None;
          used_in_call_args = false;
          used_as_late_arg = false;
        }
      in
      Hashtbl.add stats_table temp stats;
      stats

let note_temp_use stats_table temp pos =
  let stats = get_temp_stats stats_table temp pos in
  stats.use_count <- stats.use_count + 1

let note_temp_def stats_table temp pos =
  let stats = get_temp_stats stats_table temp pos in
  stats.def_count <- stats.def_count + 1

let spill_weight use_count def_count call_crossings start_pos end_pos =
  let benefit = max 1 ((4 * use_count) + (2 * def_count) + (12 * call_crossings)) in
  let span = max 1 (end_pos - start_pos + 1) in
  (benefit * 1024) / span

let fits_simm12 n = n >= -2048L && n <= 2047L

let power_of_two_shift n =
  let rec loop value shift =
    if value = 1L then if shift < 32 then Some shift else None
    else if Int64.logand value 1L <> 0L then None
    else loop (Int64.shift_right_logical value 1) (shift + 1)
  in
  if n > 0L then loop n 0 else None

let compute_temp_intervals (f : Cfg.func) =
  let live_in, live_out = compute_temp_live_sets f in
  let stats_table = Hashtbl.create (max 8 f.temp_count) in
  let hint_tables = Hashtbl.create (max 8 f.temp_count) in
  let block_ranges = Hashtbl.create (List.length f.blocks) in
  let call_sites_rev = ref [] in
  let note_operand pos = function
    | Tcg.Temp temp -> note_temp_use stats_table temp pos
    | Tcg.Imm _ -> ()
  in
  let note_instr pos is_tail = function
    | Tcg.Move (dst, src) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        note_temp_def stats_table dst def_pos;
        note_operand use_pos src;
        (match src with
        | Tcg.Temp src_temp ->
            note_move_hint hint_tables dst src_temp;
            note_move_hint hint_tables src_temp dst
        | Tcg.Imm _ -> ())
    | Tcg.Un (dst, _, src) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        note_temp_def stats_table dst def_pos;
        note_operand use_pos src
    | Tcg.Bin (dst, _, lhs, rhs) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        note_temp_def stats_table dst def_pos;
        note_operand use_pos lhs;
        note_operand use_pos rhs
    | Tcg.Load (dst, _) ->
        let def_pos = (2 * pos) + 1 in
        note_temp_def stats_table dst def_pos
    | Tcg.Store (_, value) ->
        note_operand (2 * pos) value
    | Tcg.Call (dst, _, args) ->
        let use_pos = 2 * pos in
        let def_pos = use_pos + 1 in
        if not is_tail then call_sites_rev := def_pos :: !call_sites_rev;
        Option.iter
          (fun temp ->
            note_temp_def stats_table temp def_pos;
            let stats = get_temp_stats stats_table temp def_pos in
            if not is_tail then stats.defined_by_call <- true)
          dst;
        List.iteri
          (fun i arg ->
            match arg with
            | Tcg.Temp temp ->
                let stats = get_temp_stats stats_table temp use_pos in
                stats.used_in_call_args <- true;
                stats.max_call_arg_index <-
                  Some
                    (match stats.max_call_arg_index with
                    | Some prev -> max prev i
                    | None -> i);
                if i > 0 then stats.used_as_late_arg <- true
            | Tcg.Imm _ -> ())
          args;
        List.iter (note_operand use_pos) args
  in
  let note_term pos = function
    | Cfg.Jump _ | Cfg.Return None -> ()
    | Cfg.BranchZero (cond, _, _)
    | Cfg.BranchNonZero (cond, _, _)
    | Cfg.Return (Some cond) ->
        note_operand (2 * pos) cond
    | Cfg.BranchCompare (_, lhs, rhs, _, _) ->
        let use_pos = 2 * pos in
        note_operand use_pos lhs;
        note_operand use_pos rhs
  in
  let pos = ref 0 in
  List.iter
    (fun (block : Cfg.block) ->
      let block_start = 2 * !pos in
      let body_len = List.length block.body in
      let last_is_tail =
        match (List.rev block.body, block.term) with
        | Tcg.Call (Some dst, _, args) :: _, Cfg.Return (Some (Tcg.Temp result)) ->
            dst = result && List.length args <= 8
        | _ -> false
      in
      List.iteri
        (fun i instr ->
          note_instr !pos (last_is_tail && i = body_len - 1) instr;
          incr pos)
        block.body;
      note_term !pos block.term;
      incr pos;
      Hashtbl.replace block_ranges block.label (block_start, (2 * !pos) - 1))
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
        defined_by_call = stats.defined_by_call;
        max_call_arg_index = stats.max_call_arg_index;
        used_in_call_args = stats.used_in_call_args;
        used_as_late_arg = stats.used_as_late_arg;
        call_crossings;
        spill_weight =
          spill_weight
            stats.use_count
            stats.def_count
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

let allocate_temp_regs (f : Cfg.func) =
  let intervals = compute_temp_intervals f in
  let homes = Hashtbl.create (max 8 f.temp_count) in
  let active = ref [] in
  let free_regs = ref allocatable_regs in
  let remove_reg reg regs =
    let rec loop acc = function
      | [] -> List.rev acc
      | current :: rest ->
          if current = reg then List.rev_append acc rest else loop (current :: acc) rest
    in
    loop [] regs
  in
  let interval_prefer_spill (a : interval) (b : interval) =
    match compare a.spill_weight b.spill_weight with
    | 0 -> (
        match compare a.use_count b.use_count with
        | 0 -> (
            match compare b.end_pos a.end_pos with
            | 0 -> b.temp < a.temp
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
      allocatable_temp_regs @ allowed_arg_regs interval @ allocatable_saved_regs
    else allocatable_saved_regs
  in
  let allowed_free_regs interval =
    let allowed = allowed_regs interval in
    List.filter (fun reg -> List.mem reg allowed) !free_regs
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
  (homes, saved_regs, intervals)

let compute_layout (f : Cfg.func) =
  let local_offsets = Hashtbl.create 64 in
  let temp_homes, temp_saved_regs, intervals = allocate_temp_regs f in
  let direct_params = find_direct_params f in
  let free_saved_regs =
    List.filter (fun reg -> not (List.mem reg temp_saved_regs)) allocatable_saved_regs
  in
  let global_regs = Hashtbl.create 4 in
  let rec assign_globals labels regs =
    match (labels, regs) with
    | label :: rest, reg :: free ->
        Hashtbl.add global_regs label reg;
        assign_globals rest free
    | _ -> ()
  in
  assign_globals (StringSet.elements (loop_global_labels f)) free_saved_regs;
  let saved_regs =
    Hashtbl.fold (fun _ reg regs -> reg :: regs) global_regs temp_saved_regs |> List.sort compare
  in
  let referenced_locals =
    List.fold_left
      (fun ids (id, _, _) -> IntSet.remove id ids)
      (referenced_local_ids f) direct_params
  in
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
  List.iter
    (fun (interval : interval) ->
      if not (Hashtbl.mem temp_homes interval.temp) then
        Hashtbl.add temp_homes interval.temp (TempStack (alloc_slot ())))
    intervals;
  let extra_args = max 0 (max_call_args f - 8) in
  let outgoing_area = align16 (extra_args * 4) in
  let frame_bytes = outgoing_area + (!next - 4) in
  let has_stack_temp =
    Hashtbl.fold
      (fun _ home found ->
        found
        ||
        match home with
        | TempStack _ -> true
        | TempReg _ -> false)
      temp_homes false
  in
  let uses_s0 = Hashtbl.length local_offsets > 0 || has_stack_temp in
  let saves_ra = needs_return_address f in
  let needs_frame = saves_ra || saved_regs <> [] || uses_s0 in
  {
    local_offsets;
    temp_homes;
    direct_params;
    global_regs;
    frame_size = if needs_frame then align16 frame_bytes else 0;
    outgoing_area;
    saved_regs;
    uses_s0;
    saves_ra;
  }

let emit_reg_copy ctx dst src =
  if dst <> src then emitf ctx "    addi %s, %s, 0" dst src

let emit_parallel_copies ctx copies =
  let rec loop pending =
    match pending with
    | [] -> ()
    | _ ->
        let sources = List.map snd pending in
        match List.find_opt (fun (dst, _) -> not (List.mem dst sources)) pending with
        | Some ((dst, src) as copy) ->
            emit_reg_copy ctx dst src;
            loop (List.filter (fun item -> item <> copy) pending)
        | None ->
            let _, src = List.hd pending in
            emit_reg_copy ctx "t0" src;
            loop
              (List.map
                 (fun (dst, current) -> (dst, if current = src then "t0" else current))
                 pending)
  in
  loop (List.filter (fun (dst, src) -> dst <> src) copies)

let init_direct_params ctx =
  let reg_copies = ref [] in
  List.iter
    (fun (_, temp, index) ->
      let src = Printf.sprintf "a%d" index in
      match lookup_temp_home ctx.temp_homes temp with
      | TempStack off -> emitf ctx "    sw %s, %d(s0)" src off
      | TempReg reg -> reg_copies := (reg, src) :: !reg_copies)
    ctx.direct_params;
  emit_parallel_copies ctx (List.rev !reg_copies)

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

let load_place ctx dst = function
  | Tcg.Local id ->
      emitf ctx "    lw %s, %d(s0)" dst (lookup_offset ctx.local_offsets id "local")
  | Tcg.Global label ->
      let addr = Option.value ~default:global_addr_reg (Hashtbl.find_opt ctx.global_regs label) in
      if addr = global_addr_reg then emitf ctx "    la %s, %s" addr label;
      emitf ctx "    lw %s, 0(%s)" dst addr

let store_place ctx src = function
  | Tcg.Local id ->
      emitf ctx "    sw %s, %d(s0)" src (lookup_offset ctx.local_offsets id "local")
  | Tcg.Global label ->
      let addr = Option.value ~default:global_addr_reg (Hashtbl.find_opt ctx.global_regs label) in
      if addr = global_addr_reg then emitf ctx "    la %s, %s" addr label;
      emitf ctx "    sw %s, 0(%s)" src addr

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
  | Mul, Tcg.Imm factor, rhs -> (
      match power_of_two_shift factor with
      | Some shift ->
          let rhs_reg = operand_reg ctx "t0" rhs in
          emitf ctx "    slli %s, %s, %d" dst rhs_reg shift
      | None ->
          let lhs_reg = operand_reg ctx "t0" (Tcg.Imm factor) in
          let rhs_reg = operand_reg ctx "t1" rhs in
          emit_binop ctx op dst lhs_reg rhs_reg)
  | Mul, lhs, Tcg.Imm factor -> (
      match power_of_two_shift factor with
      | Some shift ->
          let lhs_reg = operand_reg ctx "t0" lhs in
          emitf ctx "    slli %s, %s, %d" dst lhs_reg shift
      | None ->
          let lhs_reg = operand_reg ctx "t0" lhs in
          let rhs_reg = operand_reg ctx "t1" (Tcg.Imm factor) in
          emit_binop ctx op dst lhs_reg rhs_reg)
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
  | Div, lhs, Tcg.Imm divisor when (let v = Int64.to_int divisor in v > 0 && v land (v - 1) = 0 && v > 1) -> (
      let shift = let rec f v s = if v = 1L then s else f (Int64.shift_right_logical v 1) (s + 1) in f divisor 0 in
      let lhs_reg = operand_reg ctx "t0" lhs in
      if shift = 1 then begin
        emitf ctx "    srli %s, %s, 31" dst lhs_reg;
        emitf ctx "    add %s, %s, %s" dst lhs_reg dst;
        emitf ctx "    srai %s, %s, 1" dst dst
      end else begin
        emitf ctx "    srai %s, %s, %d" dst lhs_reg (shift - 1);
        emitf ctx "    srli %s, %s, %d" dst dst (32 - shift);
        emitf ctx "    add %s, %s, %s" dst lhs_reg dst;
        emitf ctx "    srai %s, %s, %d" dst dst shift
      end)
  | Mod, lhs, Tcg.Imm divisor when (let v = Int64.to_int divisor in v > 0 && v land (v - 1) = 0 && v > 1) -> (
      let shift = let rec f v s = if v = 1L then s else f (Int64.shift_right_logical v 1) (s + 1) in f divisor 0 in
      let lhs_reg = operand_reg ctx "t0" lhs in
      let tmp = "t1" in
      if shift = 1 then begin
        emitf ctx "    srli %s, %s, 31" tmp lhs_reg;
        emitf ctx "    add %s, %s, %s" tmp lhs_reg tmp;
        emitf ctx "    srai %s, %s, 1" tmp tmp
      end else begin
        emitf ctx "    srai %s, %s, %d" tmp lhs_reg (shift - 1);
        emitf ctx "    srli %s, %s, %d" tmp tmp (32 - shift);
        emitf ctx "    add %s, %s, %s" tmp lhs_reg tmp;
        emitf ctx "    srai %s, %s, %d" tmp tmp shift
      end;
      emitf ctx "    slli %s, %s, %d" tmp tmp shift;
      emitf ctx "    sub %s, %s, %s" dst lhs_reg tmp)
  | Mul, lhs, Tcg.Imm 3L -> (
      let lhs_reg = operand_reg ctx "t0" lhs in
      emitf ctx "    slli %s, %s, 1" dst lhs_reg;
      emitf ctx "    add %s, %s, %s" dst dst lhs_reg)
  | Mul, Tcg.Imm 3L, rhs -> (
      let rhs_reg = operand_reg ctx "t0" rhs in
      emitf ctx "    slli %s, %s, 1" dst rhs_reg;
      emitf ctx "    add %s, %s, %s" dst dst rhs_reg)
  | Mul, lhs, Tcg.Imm 5L -> (
      let lhs_reg = operand_reg ctx "t0" lhs in
      emitf ctx "    slli %s, %s, 2" dst lhs_reg;
      emitf ctx "    add %s, %s, %s" dst dst lhs_reg)
  | Mul, Tcg.Imm 5L, rhs -> (
      let rhs_reg = operand_reg ctx "t0" rhs in
      emitf ctx "    slli %s, %s, 2" dst rhs_reg;
      emitf ctx "    add %s, %s, %s" dst dst rhs_reg)
  | _ ->
       let lhs_reg = operand_reg ctx "t0" lhs in
       let rhs_reg = operand_reg ctx "t1" rhs in
       emit_binop ctx op dst lhs_reg rhs_reg

let emit_call_args ctx args =
  List.iteri
    (fun i arg ->
      if i >= 8 then
        let arg_reg = operand_reg ctx "t0" arg in
        emitf ctx "    sw %s, %d(sp)" arg_reg ((i - 8) * 4))
    args;
  let copies = ref [] in
  let delayed = ref [] in
  List.iteri
    (fun i arg ->
      if i < 8 then
        let dst = Printf.sprintf "a%d" i in
        match arg with
        | Tcg.Temp temp -> (
            match lookup_temp_home ctx.temp_homes temp with
            | TempReg src -> copies := (dst, src) :: !copies
            | TempStack _ -> delayed := (dst, arg) :: !delayed)
        | Tcg.Imm _ -> delayed := (dst, arg) :: !delayed)
    args;
  emit_parallel_copies ctx (List.rev !copies);
  List.iter (fun (dst, arg) -> load_operand ctx dst arg) (List.rev !delayed)

let emit_call ctx callee args =
  emit_call_args ctx args;
  emitf ctx "    call %s" callee

let restart_function ctx args =
  emit_call_args ctx args;
  init_direct_params ctx;
  List.iteri
    (fun i (param : Tcg.var) ->
      match Hashtbl.find_opt ctx.local_offsets param.id with
      | Some off -> emitf ctx "    sw a%d, %d(s0)" i off
      | None -> ())
    ctx.params;
  emitf ctx "    j %s" ctx.entry

let temp_live_out ctx label temp =
  IntSet.mem temp (table_find_or_empty ctx.live_out_temps label IntSet.empty)

let is_direct_param ctx id temp =
  List.exists
    (fun (param_id, param_temp, _) -> param_id = id && param_temp = temp)
    ctx.direct_params

let replace_temp_operand dst replacement = function
  | Tcg.Temp temp when temp = dst -> replacement
  | operand -> operand

let gen_simple_instr ctx = function
  | Tcg.Load (dst, Tcg.Local id)
    when List.exists (fun (param_id, temp, _) -> param_id = id && temp = dst) ctx.direct_params ->
      ()
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

let restore_frame ctx =
  if ctx.frame_size > 0 then begin
    List.iteri
      (fun i reg -> emitf ctx "    lw %s, %d(sp)" reg (ctx.frame_size - (12 + (4 * i))))
      ctx.saved_regs;
    if ctx.saves_ra then emitf ctx "    lw ra, %d(sp)" (ctx.frame_size - 4);
    if ctx.uses_s0 then emitf ctx "    lw s0, %d(sp)" (ctx.frame_size - 8);
    emitf ctx "    addi sp, sp, %d" ctx.frame_size
  end

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
  | Tcg.Load (dst, Tcg.Local id) when is_direct_param ctx id dst ->
      load_operand ctx "a0" (Tcg.Temp dst);
      emitf ctx "    j %s" ctx.epilogue
  | Tcg.Load (_, place) ->
      load_place ctx "a0" place;
      emitf ctx "    j %s" ctx.epilogue
  | Tcg.Store _ -> raise (Error "store cannot feed tail return directly")
  | Tcg.Call (_, callee, args) when callee = ctx.func && List.length args <= 8 ->
      restart_function ctx args
  | Tcg.Call (_, callee, args) when List.length args <= 8 ->
      emit_call_args ctx args;
      restore_frame ctx;
      emitf ctx "    j %s" callee
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
  | Tcg.Load (dst, Tcg.Local id) when is_direct_param ctx id dst ->
      let reg = operand_reg ctx "t0" (Tcg.Temp dst) in
      emit_branch_result ctx reg if_nonzero if_zero next_label
  | Tcg.Load (_, place) ->
      load_place ctx "t0" place;
      emit_branch_result ctx "t0" if_nonzero if_zero next_label
  | Tcg.Store _ -> raise (Error "store cannot feed tail branch directly")
  | Tcg.Call (_, callee, args) ->
      emit_call ctx callee args;
      emit_branch_result ctx "a0" if_nonzero if_zero next_label

let instr_operand_temps = function
  | Tcg.Move (_, Tcg.Temp temp)
  | Tcg.Un (_, _, Tcg.Temp temp)
  | Tcg.Store (_, Tcg.Temp temp) ->
      [ temp ]
  | Tcg.Bin (_, _, lhs, rhs) ->
      List.filter_map (function Tcg.Temp temp -> Some temp | Tcg.Imm _ -> None) [ lhs; rhs ]
  | Tcg.Call (_, _, args) ->
      List.filter_map (function Tcg.Temp temp -> Some temp | Tcg.Imm _ -> None) args
  | Tcg.Move (_, Tcg.Imm _)
  | Tcg.Un (_, _, Tcg.Imm _)
  | Tcg.Load _
  | Tcg.Store (_, Tcg.Imm _) ->
      []

let instr_read_regs ctx instr =
  List.filter_map
    (fun temp ->
      match lookup_temp_home ctx.temp_homes temp with
      | TempReg reg -> Some reg
      | TempStack _ -> None)
    (instr_operand_temps instr)

let emit_value_instr ctx dst = function
  | Tcg.Move (_, src) -> load_operand ctx dst src
  | Tcg.Un (_, op, src) ->
      let src_reg = operand_reg ctx "t0" src in
      emit_unop ctx op dst src_reg
  | Tcg.Bin (_, op, lhs, rhs) -> emit_binop_operands ctx op dst lhs rhs
  | Tcg.Load (_, place) -> load_place ctx dst place
  | Tcg.Store _ | Tcg.Call _ -> raise (Error "tail argument is not a pure value")

let finish_self_restart ctx =
  init_direct_params ctx;
  List.iteri
    (fun i (param : Tcg.var) ->
      match Hashtbl.find_opt ctx.local_offsets param.id with
      | Some off -> emitf ctx "    sw a%d, %d(s0)" i off
      | None -> ())
    ctx.params;
  emitf ctx "    j %s" ctx.entry

let try_direct_self_restart ctx rev_prefix args =
  if args = [] || List.length args > 8 then false
  else
    let arg_index = Hashtbl.create (List.length args) in
    let unique = ref true in
    List.iteri
      (fun i -> function
        | Tcg.Temp temp ->
            if Hashtbl.mem arg_index temp then unique := false
            else Hashtbl.add arg_index temp i
        | Tcg.Imm _ -> unique := false)
      args;
    if not !unique then false
    else
      let rec take chosen = function
        | instr :: rest -> (
            match defs_temp instr with
            | Some temp when Hashtbl.mem arg_index temp -> take (instr :: chosen) rest
            | Some _ | None -> (chosen, instr :: rest))
        | [] -> (chosen, [])
      in
      let chosen, remaining_rev = take [] rev_prefix in
      let defined =
        List.fold_left
          (fun temps instr -> Option.fold ~none:temps ~some:(fun temp -> IntSet.add temp temps) (defs_temp instr))
          IntSet.empty chosen
      in
      let independent =
        List.for_all
          (fun instr ->
            List.for_all (fun temp -> not (IntSet.mem temp defined)) (instr_operand_temps instr))
          chosen
      in
      if List.length chosen <> List.length args || not independent then false
      else
        let items =
          List.map
            (fun instr ->
              let temp = Option.get (defs_temp instr) in
              let index = Hashtbl.find arg_index temp in
              (Printf.sprintf "a%d" index, instr))
            chosen
        in
        let rec schedule done_items pending =
          match pending with
          | [] -> Some (List.rev done_items)
          | _ -> (
              match
                List.find_opt
                  (fun (dst, item) ->
                    List.for_all
                      (fun (_, other) -> item == other || not (List.mem dst (instr_read_regs ctx other)))
                      pending)
                  pending
              with
              | None -> None
              | Some item -> schedule (item :: done_items) (List.filter (fun x -> x != item) pending))
        in
        match schedule [] items with
        | None -> false
        | Some ordered ->
            List.iter (gen_simple_instr ctx) (List.rev remaining_rev);
            List.iter (fun (dst, instr) -> emit_value_instr ctx dst instr) ordered;
            finish_self_restart ctx;
            true

let gen_block ctx next_label (block : Cfg.block) =
  emitf ctx "%s:" block.label;
  match (List.rev block.body, block.term) with
  | (Tcg.Call (Some dst, callee, args) :: rev_prefix), Cfg.Return (Some (Tcg.Temp result))
    when dst = result && callee = ctx.func && try_direct_self_restart ctx rev_prefix args ->
      ()
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
  let f = schedule_func_blocks f in
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
      global_regs = layout.global_regs;
      blocks_by_label;
      live_out_temps;
      epilogue;
      func = f.label;
      entry = f.entry;
      params = f.params;
      direct_params = layout.direct_params;
      frame_size = layout.frame_size;
      saved_regs = layout.saved_regs;
      uses_s0 = layout.uses_s0;
      saves_ra = layout.saves_ra;
    }
  in
  emit ctx "    .text";
  emit ctx "    .align 2";
  if f.name = "main" then emit ctx "    .globl main";
  emitf ctx "%s:" f.label;
  if layout.frame_size > 0 then begin
    emitf ctx "    addi sp, sp, -%d" layout.frame_size;
    if layout.saves_ra then emitf ctx "    sw ra, %d(sp)" (layout.frame_size - 4);
    if layout.uses_s0 then emitf ctx "    sw s0, %d(sp)" (layout.frame_size - 8);
    List.iteri
      (fun i reg -> emitf ctx "    sw %s, %d(sp)" reg (layout.frame_size - (12 + (4 * i))))
      layout.saved_regs;
    if layout.uses_s0 then emitf ctx "    addi s0, sp, %d" layout.frame_size
  end;
  Hashtbl.iter (fun label reg -> emitf ctx "    la %s, %s" reg label) layout.global_regs;
  init_direct_params ctx;
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
  restore_frame ctx;
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
