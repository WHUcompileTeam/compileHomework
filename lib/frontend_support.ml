open Ast

type parser_state = {
  mutable next_id : int;
}

let parser_state = { next_id = 0 }

let reset_parser_state () = parser_state.next_id <- 0

let fresh_id () =
  let id = parser_state.next_id in
  parser_state.next_id <- parser_state.next_id + 1;
  id

let loc_of_pos pos =
  {
    line = pos.Lexing.pos_lnum;
    col = (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) + 1;
  }

let last_loc = ref { line = 1; col = 1 }
let last_lexeme = ref ""

let remember lexbuf =
  last_loc := loc_of_pos (Lexing.lexeme_start_p lexbuf);
  last_lexeme := Lexing.lexeme lexbuf

let remember_eof lexbuf =
  last_loc := loc_of_pos lexbuf.Lexing.lex_curr_p;
  last_lexeme := ""

let current_loc () = !last_loc
let current_lexeme () = !last_lexeme

let format_loc loc = Printf.sprintf "%d:%d" loc.line loc.col

exception Lex_error of string
exception Parse_error of string

let raise_lex_error_at loc msg =
  raise
    (Lex_error
       (Printf.sprintf "lexer error at %s: %s" (format_loc loc) msg))

let syntax_error_message () =
  let loc = current_loc () in
  let near =
    if !last_lexeme = "" then "end of file" else Printf.sprintf "%S" !last_lexeme
  in
  Printf.sprintf "parser error at %s near %s: syntax error" (format_loc loc)
    near

let raise_parse_error () = raise (Parse_error (syntax_error_message ()))
