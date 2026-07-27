exception Error of string

let strip_bom src =
  if
    String.length src >= 3
    && Char.code src.[0] = 0xEF
    && Char.code src.[1] = 0xBB
    && Char.code src.[2] = 0xBF
  then String.sub src 3 (String.length src - 3)
  else src

let parse src =
  Frontend_support.reset_parser_state ();
  let lexbuf = Lexing.from_string (strip_bom src) in
  try Grammar.program Lexer.read lexbuf with
  | Frontend_support.Parse_error msg -> raise (Error msg)
  | Parsing.Parse_error ->
      raise (Error (Frontend_support.syntax_error_message ()))
