let read_stdin () =
  let buf = Buffer.create 4096 in
  (try
     while true do
       Buffer.add_string buf (input_line stdin);
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  Buffer.contents buf

let has_opt_flag () =
  Array.exists (fun arg -> arg = "-opt") Sys.argv

let run () =
  try
    let source = read_stdin () in
    let parsed = Parser.parse source in
    let ast = if has_opt_flag () then Opt.optimize_ast parsed else parsed in
    let tcg = Tcg.of_ast ast in
    let cfg = Cfg.of_tcg tcg in
    let _cfg = if has_opt_flag () then Opt.optimize_cfg cfg else cfg in
    let analysis = Semant.analyze ast in
    let asm = Codegen.generate analysis in
    print_string (if has_opt_flag () then Asm_opt.peephole asm else asm)
  with
  | Lexer.Error msg
  | Parser.Error msg
  | Semant.Error msg
  | Codegen.Error msg ->
      prerr_endline msg;
      exit 1
