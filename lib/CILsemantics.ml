open CILsyntax

type ns = string list

let option_value_error mv errs =
  match mv with
  | Some v -> v
  | None -> failwith errs

let substitute rules fpars apars =
  let ftoapairs = (List.combine fpars apars) in
  let substitute_t qn = 
    match
      (List.find_opt 
        (fun (fp, ap) -> 
          match fp with
          | PARTYPE, pt -> qn = [pt]
          | _ -> false
        )
        ftoapairs)
    with
    | Some (fp, ap) -> ap
    | None -> qn
  in
  List.rev_map
    (function
    | CILCALL (mqn, apars) -> CILCALL 
        (
          mqn, 
          List.map substitute_t apars
        )
    | CILALLOW (src, dst, perms) -> CILALLOW (substitute_t src, substitute_t dst, perms)
    | r -> r)
  rules

let rec sem_t1R rules rho sigma =
    List.rev_map
    (fun rule -> sem_t1 rule rho sigma)
    rules

and sem_t1 rule rho sigma =
  match rule with
  | CILBLOCK (dn, rules) -> 
      let rules' = sem_t1R rules rho ((CILenv.enterblock (List.hd sigma) dn) :: List.tl sigma)
      in
      CILBLOCK (dn, rules')     
  | CILBLOCKINHERIT qn ->
      (match CILenv.eval_b_bar qn rho sigma with
        | Some (fn, _) -> CILBLOCKINHERIT fn
        | None -> failwith ("undefined block to inherit " ^ qn_tostring qn))
  | _ -> rule

let last_and_list lst =
  let rvlst = List.rev lst 
  in
  (List.hd rvlst, List.rev (List.tl rvlst))

let rec sem_t2R rules rho ns = 
  List.fold_left
  (fun xrho xrho' -> CILenv.union xrho xrho')
  rho
  (List.rev_map
    (fun rule -> sem_t2 rule rho ns)
    rules)

and sem_t2 rule rho ns = 
  match rule with 
  | CILBLOCKINHERIT qn -> 
      (match CILenv.eval_b_bar qn rho [] with
        | Some (_, rules) ->
          let rho' = sem_t2R rules rho qn
          in CILenv.rho_plus_rho_m ns qn rho rho'         
        | None -> failwith "cannot resolve a block name in t2")
  | CILBLOCK (dn, rs) -> sem_t2R rs rho (CILenv.enterblock ns dn)
  | _ -> rho

let rec sem_t3R rules rho sigma = 
  List.fold_left
  (fun xrho xrho' -> CILenv.union xrho xrho')
  rho
  (List.rev_map
    (fun rule -> sem_t3 rule rho sigma)
    rules)

and sem_t3 rule rho sigma = 
  match rule with 
  | CILCALL (qn, pars) ->
      let csi = CILenv.cdm qn rho sigma
      in
      CILenv.rho_plus_csi rho (List.hd sigma) csi
  | CILBLOCKINHERIT qn ->
      let (_, rules) = 
        option_value_error
          (CILenv.eval_b_bar qn rho [])
          "cannot resolve a block name in t3"
      and (_, ns) = last_and_list qn in
      let rho' = sem_t3R rules rho (sigma @ [ns])
      in CILenv.rho_plus_rho (List.hd sigma) qn rho' rho'
  | CILBLOCK (dn, rs) -> sem_t3R rs rho ((CILenv.enterblock (List.hd sigma) dn) :: List.tl sigma)
  | _ -> rho

let rec sem_Call_AR rules rho sigma csi = 
  List.concat
  (List.rev_map
    (fun rule -> sem_Call_A rule rho sigma csi)
    rules)

and sem_Call_A rule rho sigma csi =
  match rule with
  | CILCALL (qn, apars) ->
    let rho' = CILenv.rho_intersec_csi rho [CILenv.fresh] csi 
    in
    let (_, fpars, rules, csi', clousure) =
      option_value_error
        (CILenv.eval_m_bar qn rho' ([CILenv.fresh] :: sigma))
        "cannot resolve a macro name in sem_Call_A"
    in let eapars =
      option_value_error
        (CILenv.eval_pars_bar apars fpars rho' ([CILenv.fresh] :: sigma))
        "cannot resolve a macro parameters in sem_Call_A"
    in
    let rules' = substitute rules fpars eapars
    in
    sem_Call_AR rules' rho (clousure @ sigma) csi'
  | _ -> 
    let rho' = CILenv.rho_intersec_csi rho [CILenv.fresh] csi
    in
    sem_A rule rho' ([CILenv.fresh]::sigma)

and sem_AR rules rho sigma = 
  List.concat
  (List.rev_map
    (fun rule -> sem_A rule rho sigma)
    rules)

and sem_A rule rho sigma = 
  match rule with 
  | CILALLOW (src, dst, perms) ->
      let gsrc =
        option_value_error
          (CILenv.eval_tora_bar src rho sigma)
          "undefined type"
      and gdst = 
        option_value_error
          (CILenv.eval_tora_bar dst rho sigma)
          "undefined type"
      in [(gsrc, gdst)]
  | CILBLOCK (dn, rs) -> 
      sem_AR rs rho ((CILenv.enterblock (List.hd sigma) dn) :: List.tl sigma)
  | CILBLOCKINHERIT qn ->
      let (_, rules) = 
        option_value_error
          (CILenv.eval_b_bar qn rho [])
          "cannot resolve a block name in sem_A"
      and (_, ns) = 
      last_and_list qn
      in sem_AR rules rho (sigma @ [ns])
  | CILCALL (qn, apars) ->
      let (mgn, fpars, rs, csi, clousure) = 
        option_value_error
          (CILenv.eval_m_bar qn rho sigma)
          "cannot resolve a macro name in sem_A"
      in 
      let csi' = CILenv.cdm qn rho sigma 
      and csi'' = CILenv.cdm qn rho (clousure @ sigma) 
      and ns = List.hd sigma
      in
      let rho'' = CILenv.rho_minus_csi rho ns csi''
      in
      let eapars =
        option_value_error
          (CILenv.eval_pars_bar apars fpars rho'' sigma)
          "cannot resolve a macro parameters in sem_A"
      in
      let rho' = 
      CILenv.fake_fr_rho rho ns csi' in
      let rs' = substitute rs fpars eapars in
      sem_Call_AR rs' rho' (clousure @ sigma) csi
  | _ -> []

let paper_semantics rules = 
  (* print_endline "RULES\n";
  CILsyntax.print rules; *)

  let irho = CILenv.sem_initialrhoR rules ["#"] in
  (* print_endline "######### INITIAL RHO #########\n"; *)
  (* print_endline "######### INITIAL RHO #########\n";
  CILenv.print irho;
  print_endline "###############################\n"; *)

  let rules' = sem_t1R rules irho [["#"]] in     
  let rho =  CILenv.sem_initialrhoR rules' ["#"] in
  (* print_endline "######### RHO AFTER T1 #########\n"; *)
  (* print_endline "######### RHO AFTER T1 #########\n";
  CILenv.print rho;
  print_endline "###############################\n"; *)

  let rho' = sem_t2R rules' rho ["#"] in 
  (* print_endline "\n######### RHO AFTER T2 #########\n"; *)
  (* print_endline "\n######### RHO AFTER T2 #########\n";
  CILenv.print rho';
  print_endline "###############################\n"; *)

  let rho'' = sem_t3R rules' rho' [["#"]] in
  (* print_endline "######### RHO AFTER T3 #########\n"; *)
  (* print_endline "######### RHO AFTER T3 #########\n";
  CILenv.print rho'';
  print_endline "###############################\n"; *)

  let allows = sem_AR rules' rho'' [["#"]] in 
  (* print_endline "######### ALLOWS AFTER E_A #########\n";
  List.iter
    (fun (src,dst) -> 
      print_string ("permission from " ^ (qn_tostring src) ^ " to " ^ (qn_tostring dst) ^ "\n"))
    allows;
  print_endline "###############################\n"; *)

  print_endline "SEMANTIC COMPLETED ";
  allows

