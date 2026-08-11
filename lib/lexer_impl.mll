{
open Frontend_support

let keyword_or_id = function
  | "int" -> Grammar.KW_INT
  | "void" -> Grammar.KW_VOID
  | "const" -> Grammar.KW_CONST
  | "if" -> Grammar.KW_IF
  | "else" -> Grammar.KW_ELSE
  | "while" -> Grammar.KW_WHILE
  | "break" -> Grammar.KW_BREAK
  | "continue" -> Grammar.KW_CONTINUE
  | "return" -> Grammar.KW_RETURN
  | name -> Grammar.ID name

let loc lexbuf = loc_of_pos (Lexing.lexeme_start_p lexbuf)

let token lexbuf value =
  remember lexbuf;
  value

let eof_token lexbuf =
  remember_eof lexbuf;
  Grammar.EOF

let lex_error lexbuf msg = raise_lex_error_at (loc lexbuf) msg
}

rule read = parse
  | [' ' '\t' '\012' '\r']+ { read lexbuf }
  | '\n' { Lexing.new_line lexbuf; read lexbuf }
  | "//" { line_comment lexbuf }
  | "/*" { block_comment lexbuf }
  | '(' { token lexbuf Grammar.LPAR }
  | ')' { token lexbuf Grammar.RPAR }
  | '{' { token lexbuf Grammar.LBRACE }
  | '}' { token lexbuf Grammar.RBRACE }
  | ';' { token lexbuf Grammar.SEMI }
  | ',' { token lexbuf Grammar.COMMA }
  | "==" { token lexbuf Grammar.EQEQ }
  | "!=" { token lexbuf Grammar.BANGEQ }
  | "<=" { token lexbuf Grammar.LESSEQ }
  | ">=" { token lexbuf Grammar.GREATEREQ }
  | "&&" { token lexbuf Grammar.ANDAND }
  | "||" { token lexbuf Grammar.OROR }
  | '=' { token lexbuf Grammar.ASSIGN }
  | '+' { token lexbuf Grammar.PLUS }
  | '-' { token lexbuf Grammar.MINUS }
  | '*' { token lexbuf Grammar.STAR }
  | '/' { token lexbuf Grammar.SLASH }
  | '%' { token lexbuf Grammar.PERCENT }
  | '!' { token lexbuf Grammar.BANG }
  | '<' { token lexbuf Grammar.LESS }
  | '>' { token lexbuf Grammar.GREATER }
  | ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
      { token lexbuf (keyword_or_id (Lexing.lexeme lexbuf)) }
  | ['0'-'9']+
      {
        let raw = Lexing.lexeme lexbuf in
        let value =
          try Int64.of_string raw
          with Failure _ -> lex_error lexbuf ("invalid integer literal " ^ raw)
        in
        token lexbuf (Grammar.NUMBER value)
      }
  | eof { eof_token lexbuf }
  | _ { lex_error lexbuf (Printf.sprintf "unexpected character %C" (Lexing.lexeme_char lexbuf 0)) }

and line_comment = parse
  | '\n' { Lexing.new_line lexbuf; read lexbuf }
  | eof { eof_token lexbuf }
  | _ { line_comment lexbuf }

and block_comment = parse
  | "*/" { read lexbuf }
  | '\n' { Lexing.new_line lexbuf; block_comment lexbuf }
  | eof { lex_error lexbuf "unterminated block comment" }
  | _ { block_comment lexbuf }
