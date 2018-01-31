open Camlp4.PreCast

type sPL_token = 
  | IDENTIFIER of string
  | INT_LIT of int * string
  | CHAR_LIT of char * string
  | STRING of string * string
  | TRUE | FALSE
  | INT_TYP | BOOL_TYP
  | PLUS | UMINUS | MINUS | STAR | DIV
  | EQ |NEQ | LT |LTEQ | GT |GTEQ 
  | AND | OR | NEG
  | LETWORD | INWORD | ENDWORD
  | FUN | RECFUN | RARROW
  | OPAREN | CPAREN
  | OBRACE | CBRACE
  | OSQBRACE | CSQBRACE
  | IFWORD | THENWORD | ELSEWORD

  (* Tokens define relational algebra *)

  | RELATIONWORD | ROWWORD             (* For syntax *)
  | JOIN | PROJECT | SELECTION         (* To denote join and projection operators. Add more if requried. *)
  | COLON | SEMICOLON | COMMA |HASHTAG        (* To denote newly added separators *)
  | EOF

  (* End of token definitons for relational algebra *)

  
module type SPLTokenS = Camlp4.Sig.Token with type t = sPL_token

module SPL_token = struct
  open Format
  module Loc = Loc
  type t = sPL_token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with
    | IDENTIFIER s | INT_LIT(_,s) | CHAR_LIT(_,s) | STRING(_,s) -> s
    | TRUE -> "true" | FALSE -> "false"
    | INT_TYP -> "int" | BOOL_TYP -> "bool"
    | PLUS -> "+" | UMINUS -> "~" | MINUS -> "-" | STAR -> "*" | DIV -> "/"

    | EQ -> "=" | NEQ -> "!=" | LT -> "<" | LTEQ -> "<=" | GT -> ">" | GTEQ -> ">="

    | AND -> "&" | OR -> "|" | NEG -> "\\"
    | LETWORD -> "let" | INWORD -> "in" | ENDWORD -> "end"
    | FUN -> "fun" | RECFUN -> "recfun" | RARROW -> "->"
    | OPAREN -> "(" | CPAREN -> ")"
    | OBRACE -> "{" | CBRACE -> "}"
    | OSQBRACE -> "[" | CSQBRACE -> "]"
    | IFWORD -> "if" | THENWORD -> "then" | ELSEWORD -> "else"
    (* To define relations *)
    | RELATIONWORD -> "relation"
    | ROWWORD -> "row"
    | JOIN -> "|><|"| PROJECT -> "|||" | SELECTION -> "$$"
    | COLON -> ":"  | SEMICOLON -> ";" | COMMA -> "," | HASHTAG -> "#"
    | EOF -> ""

  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false

  let extract_string t = match t with
    | IDENTIFIER s | INT_LIT(_,s) | CHAR_LIT(_,s) | STRING(_,s) -> s
    | _ -> ""

  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t,Loc.t) Camlp4.Sig.stream_filter

    type t = {is_kwd: string -> bool;
              mutable filter : token_filter}

    let mk is_kwd = {is_kwd = is_kwd;
                     filter = (fun s -> s)}

    let filter x = fun strm -> x.filter strm

    let define_filter x f = x.filter <- f x.filter

    let keyword_added _ _ _ = ()

    let keyword_removed _ _ = ()
  end

end

module Error = Camlp4.Struct.EmptyError
