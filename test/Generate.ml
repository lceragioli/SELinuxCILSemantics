open SELinuxCILSem.CILsyntax

let range n m =
  if ((1 + m) - n) < 0 then [] else
  List.init 
    ((1 + m) - n)
    (fun x -> n + x)

let names num =
  List.init 
    num
    (fun i -> String.make 1 (Char.chr (i + 97)))

let randElem = function
  | [] -> failwith "random element from emptylist is undefined"
  | [el] -> el
  | lst ->
    List.nth
      lst
      (Random.int (List.length lst))

let randDName = randElem 

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let interval names = 
  let num = ref 0 
  and max = (List.length names) in
  for i = 1 to max do
    (* print_int !num;
    print_endline " <-- !num"; *)
    num := !num + (pow 2 (max - i))
  done;
  !num

let rec getnum_from_interval' i n max =
  (* print_int i;
  print_endline " <-- i"; *)
  let endint = pow 2 (max - i) in
  if n <= endint then i
  else (getnum_from_interval' (i + 1) (n - endint) max)

let getnum_from_interval n max =
  (* print_int n;
  print_endline " <-- n in getnum"; *)
  getnum_from_interval' 1 n max
  
let randQName nsnames dnames =
  let interval = interval nsnames in
  let length = if interval = 0 || nsnames = [] then 1 else 
    getnum_from_interval
    (Random.int interval)
    (List.length nsnames)
  in
  List.init
    length
    (function
      | 0 -> if length > 1 then randDName ("#" :: nsnames) else randDName dnames
      | n -> if n < (length - 1) then randDName nsnames else randDName dnames
    )

module SS = Set.Make (String)

type usednames = {tn : SS.t; bn : SS.t; mn : SS.t}
let unames_union un un' = 
  { 
    tn = SS.union un.tn un'.tn;
    bn = SS.union un.bn un'.bn; 
    mn = SS.union un.mn un'.mn
  }

let rec genMRand n names =
  if n < 1 then ({tn = SS.empty; bn = SS.empty; mn = SS.empty}, []) else 
    let (unames, randR) = genMRand (n - 1) names 
    and tname = randDName names in
    ({unames with tn = SS.add tname unames.tn}, (CILTYPE tname) :: randR)

let rec genBRand n names =
  if n < 1 then ({tn = SS.empty; bn = SS.empty; mn = SS.empty}, []) else 
    match (Random.int 3) with
    | 0 -> 
        let (unames, randR) = genBRand (n - 1) names 
        and tname = randDName names in
        ({unames with tn = SS.add tname unames.tn}, (CILTYPE tname) :: randR)
    | 1 -> 
        let m = Random.int n in 
        let (unames, randR) = genBRand m names 
        and (unames', randR') = genBRand ((n - m) - 1) names in
        let unames'' = unames_union unames unames'
        and bname = randDName names in
        ({unames'' with bn = SS.add bname unames''.bn}, (CILBLOCK (bname, randR)) :: randR')
    | 2 ->
        let m = Random.int n in 
        let (unames, randR) = genMRand m names 
        and (unames', randR') = genBRand ((n - m) - 1) names in
        let unames'' = unames_union unames unames'
        and mname = randDName names in
        ({unames'' with mn = SS.add mname unames''.mn}, (CILMACRO (randDName names, [(PARTYPE, "x")], randR)) :: randR')
    | _ -> failwith "random grater than 3"

let randTQName unames =
  randQName (SS.elements unames.bn) (SS.elements unames.tn)

let randBQName unames =
  randQName (SS.elements unames.bn) (SS.elements unames.bn)
  
let randMQName unames =
  randQName (SS.elements unames.bn) (SS.elements unames.mn)

let genComm unames =
  match (Random.int 3) with
    | 0 ->
        CILALLOW (randTQName unames, randTQName unames, Name ["permission"])
    | 1 ->
        if SS.is_empty unames.mn then
          CILALLOW (randTQName unames, randTQName unames, Name ["permission"])
        else CILCALL (randMQName unames,  [randTQName unames])
    | 2 ->
        if SS.is_empty unames.bn then
          CILALLOW (randTQName unames, randTQName unames, Name ["permission"])
        else CILBLOCKINHERIT (randBQName unames)
    | _ -> failwith "random grater than 3"

type locus = 
      | Global
      | Block of dn list
      | Macro of dn list

let rec add_command com rules = function
  | Global | Block [] | Macro [] -> com :: rules
  | Block (bn :: bns) ->
    List.rev_map
      (function
        | CILBLOCK (bn', rules') ->
            if bn = bn' then CILBLOCK (bn', add_command com rules' (Block bns)) else CILBLOCK (bn', rules')
        | rule -> rule)
      rules
  | Macro (bn :: bns) ->
    if bns = [] then
      List.rev_map
        (function
          | CILBLOCK (bn', rules') ->
              if bn = bn' then CILBLOCK (bn', add_command com rules' (Block bns)) else CILBLOCK (bn', rules')
          | rule -> rule)
        rules
    else
      List.rev_map
        (function
          | CILMACRO (mn, pars, rules') ->
              if bn = mn then CILMACRO (mn, pars, add_command com rules' (Macro bns)) else CILMACRO (mn, pars, rules')
          | rule -> rule)
        rules

let rec all_locus = function
  | [] -> [Global]
  | CILBLOCK (dn, rules) :: rules' ->
      let locus = all_locus rules
      and locus' = all_locus rules' in
      List.rev_append
        locus'
        (
          List.rev_map
          (function
            | Block ls -> Block (dn :: ls)
            | Macro ls -> Macro (dn :: ls)
            | Global -> Global
          )
          locus
        )
  | CILMACRO (dn, _, _) :: rules ->
    let locus = all_locus rules in
      (Macro [dn]) :: locus
  | _ :: rules -> all_locus rules

let rec no_types = function
    | [] -> true
    | (CILTYPE _) :: rules -> false
    | (CILBLOCK (_, rules)) :: rules' ->
        (no_types rules) && (no_types rules')
    | (CILMACRO (_, _, rules)) :: rules' ->
        (no_types rules) && (no_types rules')
    | _ :: rules -> no_types rules
        
let genRand ndec ncom names =
  let (unames, decs) = genBRand ndec names in
  if no_types decs then [] else
  let locus = all_locus decs
  and commans =
    List.init ncom (fun _ -> genComm unames) in
  List.fold_left
    (fun rules com ->
      match com with
      | CILBLOCKINHERIT _ ->
          let valid_locus = List.filter
            (function 
              | Macro _ -> false
              | _ -> true)
            locus
          in
          add_command com rules (randElem valid_locus)
      | _  ->  add_command com rules (randElem locus)
    )
    decs
    commans

