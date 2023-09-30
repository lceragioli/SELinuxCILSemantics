
module OrderList (Ord : Stdlib__set.OrderedType) = struct
  include List
  type t = Ord.t list
  let compare = List.compare Ord.compare
end;;

module OrderPair (Ord1 : Stdlib__set.OrderedType) (Ord2 : Stdlib__set.OrderedType) = struct
  type t = Ord1.t * Ord2.t
  let compare (a, b) (c, d) = 
    if Ord1.compare a c == 0 then Ord2.compare b d else Ord1.compare a c
end;;

module StringList = OrderList (String)
module StSL = OrderPair (String) (StringList)
module SS = Set.Make (String)
module SM = Map.Make (String)
module SLM = Map.Make (StringList)

let option_value_error mv errs =
  match mv with
  | Some v -> v
  | None -> failwith errs

let last_and_list lst =
  let rvlst = List.rev lst 
  in
  (List.hd rvlst, List.rev (List.tl rvlst))

let rec listminus list list' =
  (* listminus list list' returns either
     - Some list'' - where list'' is the postfix of list where list' is removed
     - None - if list' is not a prefix of list
  *)
  if list' = [] then Some list
  else if list = [] then None
  else if List.hd list = List.hd list' then
    listminus (List.tl list) (List.tl list')
  else None
  