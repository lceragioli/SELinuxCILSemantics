let _ =
  if Array.length Sys.argv != 2 then
    failwith "Arguments <CIL-input-file> is needed";
  let in_file = open_in Sys.argv.(1) in
  let lexbuf = Lexing.from_channel in_file in
  let config' = 
    (SELinuxCILSem.CILparser.main SELinuxCILSem.CILlexer.token lexbuf) in
  let config =
    SELinuxCILSem.CILsyntax.removeIN config' in
  print_endline " --> closing configfile\n";
  close_in in_file;
  print_endline " --> computing semantics\n";
  try
    (
    let semantics = SELinuxCILSem.CILsemanticsE.get_semantics (config)
    in let semAllows =
      List.map 
        (fun (a,b,c) -> (a,c))
      semantics.allows
    in List.iter
      (fun (src, dst) -> 
        print_string (String.concat "." src);
        print_string " - ";
        print_string (String.concat "." dst);
        print_string "\n"
        )
        semAllows
    )
  with 
    | Not_found -> (
        failwith "Not Found in computing semantics")
    | Failure s -> (
        failwith ("Failed computing semantics " ^ s))

  
