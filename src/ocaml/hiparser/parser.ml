open FirrtlParser

let read_line_at file line =
  if line <= 0 then ""
  else
    try
      let ic = open_in file in
      let current = ref 1 in
      let result = ref "" in
      (try
         while !current <= line do
           let l = input_line ic in
           if !current = line then result := l;
           incr current
         done
       with End_of_file -> ());
      close_in ic;
      !result
    with _ -> "" 

let hiparse file =
  let ch = open_in file in
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_lnum = 1 };
  try
    let ast = FirrtlParser.file FirrtlLexer.token lexbuf in
    close_in ch;
    ast
  with
  | Parsing.Parse_error ->
      let line = FirrtlLexer.get_lnum () in
      let line_content = read_line_at file line in
      Printf.eprintf "Syntax error at %s line %d\n%s\n" file line line_content;
      close_in ch;
      exit 1
  | FirrtlLexer.Error msg -> 
      let line = FirrtlLexer.get_lnum () in
      let line_content = read_line_at file line in
      Printf.eprintf "Lexical error at %s line %d: %s\n%s\n" file line msg line_content;
      close_in ch;
      exit 1
  | e ->
      Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string e);
      close_in ch;
      exit 1