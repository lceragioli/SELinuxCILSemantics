open SELinuxCILSem.CILsyntax

exception Timeout

let max_time = 60.

let parse_sesearch file =
  let allows = ref [] in
  try
    while true do
      let allowline = input_line file in
      try
        let fst = String.split_on_char ':' allowline in
        let parts = String.split_on_char ' ' (List.nth fst 0) in
        allows := (List.nth parts 1, List.nth parts 2) :: !allows;
      with Failure _ -> ()
    done;
    !allows
  with End_of_file -> !allows

let rmge xqn = 
    List.filter
    (fun s -> s <> "#")
    xqn

module OrderPair (Ord1 : Stdlib__set.OrderedType) (Ord2 : Stdlib__set.OrderedType) = struct
  type t = Ord1.t * Ord2.t
  let compare (a, b) (c, d) = 
    if Ord1.compare a c == 0 then Ord2.compare b d else Ord1.compare a c
end;;
  
module SP = OrderPair (String) (String)
  
module SPS = Set.Make (SP)

let compare actualAllows semAllows =
  let semAllowsStr = 
    List.rev_map
      (fun (src, dst) -> (qn_tostring (rmge src), qn_tostring (rmge dst)))
      semAllows
  in
  let aAllowSet = SPS.of_list actualAllows 
  and sAllowSet = SPS.of_list semAllowsStr in 
  (* it returns (missing, unexpected) *)
  (SPS.diff aAllowSet sAllowSet, SPS.diff sAllowSet aAllowSet)

let diff_to_string (missing, unexpected) =
  let sps_to_string sps =
    String.concat "\n"
    (
      List.map
      (fun (st, st') -> st ^ " - " ^ st')
      (SPS.elements sps)
    ) 
  in
  "Missing (in the actual permission but not in the semantics):\n" ^ (sps_to_string missing) ^ 
  "\nUnexpected (in the semantics but not in the actual permission)\n" ^ (sps_to_string unexpected)

(** [dir_is_empty dir] is true, if [dir] contains no files except
 * "." and ".."
 *)
 let dir_is_empty dir =
  Array.length (Sys.readdir dir) = 0

(** [dir_contents] returns the paths of all regular files that are
 * contained in [dir]. Each file is a path starting with [dir].
  *)
let dir_contents dir =
  let rec loop result = function
    | f::fs when Sys.is_directory f ->
          Sys.readdir f
          |> Array.to_list
          |> List.map (Filename.concat f)
          |> List.append fs
          |> loop result
    | f::fs -> loop (f::result) fs
    | []    -> result
  in
    loop [] [dir]

let _ =
  let dir = "testCases" in
  print_endline "\n++++ Testing the efficient semantics with handcrafted tests ++++\n";
  let failures = ref [] in
  let files = dir_contents dir in
  List.iter
  (fun file ->
    print_endline ("FILE: " ^ file);
    if Sys.command ("secilc -o out.temp " ^ file ) = 0 then
      (
      print_string file;
      print_endline " <-- is a valid configuration";
      if Sys.command ("sesearch --allow out.temp > sesearchout.tmp") <> 0 then failwith "generic error in sesearch";
      let ic = open_in "sesearchout.tmp" in
      print_endline " --> parsing sesearch output";
      let actualAllows = parse_sesearch ic in
      close_in ic;
      print_endline " --> opening configfile";
      let filehand = open_in file in
      let lexbuf = Lexing.from_channel filehand in
      let config = SELinuxCILSem.CILparser.main SELinuxCILSem.CILlexer.token lexbuf in
      print_endline " --> closing configfile";
      close_in filehand;
      print_endline " --> computing semantics";
      let start = Sys.time () in
      let alarm = Gc.create_alarm (fun () ->
          if Sys.time () -. start > max_time
          then raise Timeout) in
      let () = try
        (
              let semantics = SELinuxCILSem.CILsemanticsE.get_semantics (config)
              in let semAllows =
                List.map 
                  (fun (a,b,c) -> (a,c))
                semantics.allows
              in
              print_endline " --> comparing";
              let (miss, unexp) = compare actualAllows semAllows in
              print_endline " --> diff computed";
              if not (SPS.is_empty miss && SPS.is_empty unexp) then
                (
                  failures := file :: !failures;
                  if Sys.command ("echo a > " ^ file ^ ".diff") <> 0 then failwith "generic error in diff";
                  print_endline " --> opening diff file";
                  let oc' = open_out (file ^ ".diff") in
                  Printf.fprintf oc' "%s\n" (diff_to_string (miss, unexp));
                  print_endline " --> closing diff file";
                  close_out oc';
                )
            )
          with 
          | Timeout -> (
            failures := file :: !failures;
            if Sys.command ("echo non-termination_in_CIL_semantics > " ^ file ^ ".diff") <> 0 then failwith "generic error in diff";
            )
          | Not_found -> (
              failures := file :: !failures;
              if Sys.command ("echo unexpected_error_in_CIL_semantics > " ^ file ^ ".diff") <> 0 then failwith "generic error in diff")
          | Failure s -> (
              failures := file :: !failures;
              if Sys.command ("echo unexpected_error_in_CIL_semantics > " ^ file ^ ".diff") <> 0 then failwith "generic error in diff")
        in Gc.delete_alarm alarm;
      )
      else
        (
          print_endline " <-- is not a valid configuration";
        )
    )
  files;
  print_endline ("\n+++ Results of testing the efficient semantics +++\n");
  print_string "Failed Tests\n----------\nNumer: ";
  print_int (List.length !failures);
  print_endline ("\nTests: " ^ (String.concat ", " !failures))

  
