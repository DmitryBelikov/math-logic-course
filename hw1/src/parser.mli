type token =
  | VAR of (string)
  | IMPL
  | OR
  | AND
  | NOT
  | OPEN
  | CLOSE
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree
