open Generate
open SELinuxCILSem.CILsyntax
open SELinuxCILSem.CILsemantics

let configname = "GeneratedTestCases/config-"
let outname = "GeneratedTestCases/out-"

let preamble = "
(handleunknown allow)

(policycap open_perms)
(category c0)
(categoryorder (c0))
(sensitivity s0)
(sensitivityorder (s0))
(sensitivitycategory s0 (c0))
(level systemLow (s0))
(levelrange low_low (systemLow systemLow))
(sid kernel)
(sidorder (kernel))
(sidcontext kernel unconfined.sid_context)

; Define object_r role. This must be assigned in CIL.
(role object_r)

; The unconfined namespace:
(block unconfined
	(user user)
	(userrange user (systemLow systemLow))
	(userlevel user systemLow)
	(userrole user role)
	(role role)
	(type process)
	(roletype object_r process)
	(roletype role process)

	; Define a SID context:
	(context sid_context (user role process low_low))

	(type object)
	(roletype object_r object)
)
(classorder (folder file))
(class file (read write open getattr))
(classpermission fileread)
(classpermissionset fileread (file (read)))
(class folder ())
"

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
  (* returns (missing, unexpected) *)
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

let _ =
  if Array.length Sys.argv != 5 then
    failwith "Arguments <max-declaration-num> <max-commands-num> <max-names-num> <config-num> are needed";
  let maxdecnum = int_of_string Sys.argv.(1) 
  and maxcomnum = int_of_string Sys.argv.(2)
  and maxnamesNum = int_of_string Sys.argv.(3)
  and configNum = int_of_string Sys.argv.(4) in
  print_endline "\n++++ Testing the paper semantics with randomly generated tests ++++\n";
  Random.self_init();
  let log = open_out "log.tmp" in
  let problems = ref [] in
  let confnum = ref 0 in
  for decnum = 1 to maxdecnum do
    for comnum = 1 to maxcomnum do
      for namesNum = 1 to maxnamesNum do 
        for _ = 0 to configNum do
          confnum := !confnum + 1;
          let config = genRand decnum comnum (names namesNum) in
          print_string "\nConfig. Num. ";
          print_int (!confnum + 1);
          print_newline ();
          let file = configname ^ (string_of_int !confnum) ^ ".cil" in 
          if Sys.command ("echo a > " ^ file) <> 0 then failwith "generic error in echo a";
          let oc = open_out file in
          Printf.fprintf oc "%s\n%s\n" preamble (conf_to_string config);
          close_out oc;
          if Sys.command ("secilc -o " ^ outname ^ (string_of_int !confnum) ^ ".out " ^ file ^ "" ) = 0 then
            (
            Printf.fprintf log "%n" !confnum;
            Printf.fprintf log " <-- is a valid configuration\n";
            if Sys.command ("sesearch --allow " ^ outname ^ (string_of_int !confnum) ^ ".out > sesearchout.tmp") <> 0 then failwith "generic error in  sesearch";
            let ic = open_in "sesearchout.tmp" in
            let actualAllows = parse_sesearch ic in
            close_in ic;
            let semAllows = paper_semantics config in
            let (miss, unexp) = compare actualAllows semAllows in
            if not (SPS.is_empty miss && SPS.is_empty unexp) then
              (
                if Sys.command ("echo a > " ^ outname ^ (string_of_int !confnum) ^ ".diff") <> 0 then failwith "generic error in diff";
                let oc' = open_out (outname ^ (string_of_int !confnum) ^ ".diff") in
                Printf.fprintf oc' "%s\n" (diff_to_string (miss, unexp));
                close_out oc';    
                problems := !confnum :: !problems
              ) 
            else
              (
                print_endline "no differences detected" 
              )
            )
          else
            (
            print_int !confnum;
            print_endline " <-- is not a valid configuration";
            Sys.remove file;
            )
        done
      done
    done
  done;
  Printf.fprintf stdout "Number of Errors: %n\n" (List.length !problems); 
  print_string "Problematic Configurations: ";
  List.iter
    (fun prob -> 
        print_int (prob);
        print_newline ();
    )
    !problems;
  print_newline ();
  close_out log
