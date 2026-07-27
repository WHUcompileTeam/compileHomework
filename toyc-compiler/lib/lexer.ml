exception Error of string

let read lexbuf =
  try Lexer_impl.read lexbuf
  with Frontend_support.Lex_error msg -> raise (Error msg)
