open BatPervasives

include Log.Make(struct let name = "ark.featureTree" end)
    
(* feature vector *)
type fv = int array [@@deriving ord]

let fv_leq a b =
  let len = Array.length a in
  let rec loop i =
    i == len
    || (a.(i) <= b.(i) && loop (i + 1))
  in
  loop 0

type 'a node =
  { value : int;
    left : 'a tree;
    right : 'a tree }

and 'a tree =
  | Leaf of (fv * ('a list)) list
  | Node of 'a node

type 'a t =
  { features : 'a -> fv;
    tree : 'a tree }

let bucket_size = 4

let empty features =
  { features = features;
    tree = Leaf [] }

let rec insert_bucket fv elt = function
  | (fv', elts)::xs ->
    begin match compare_fv fv fv' with
      | 0 -> (fv, elt::elts)::xs
      | x when x < 0 -> (fv,[elt])::((fv', elts)::xs)
      | _ -> (fv',elts)::(insert_bucket fv elt xs)
    end
  | xs -> (fv,[elt])::xs

let rec mk_tree feature bucket =
  if List.length bucket <= bucket_size || feature < 0 then
    Leaf bucket
  else
    let bucket =
      BatList.stable_sort
        (fun (fv,_) (fv',_) -> Pervasives.compare fv.(feature) fv'.(feature))
        bucket
    in
    let split_value =
      let rec split n left right =
        if n = 0 then
          (left, right)
        else
          match right with
          | r::rs -> split (n - 1) (r::left) right
          | [] -> assert false
      in
      let rec go ls rs value =
        match ls, rs with
        | ((fv,_)::ls', _) when fv.(feature) < value -> fv.(feature)
        | (_, (fv,_)::rs') when fv.(feature) > value -> value
        | (_::ls', _::rs') -> go ls' rs' value
        | (_, _) -> max (value - 1) 0
      in
      match split (bucket_size / 2 + 1) [] bucket with
      | (left, (fv,_)::right) -> go left right fv.(feature)
      | _ -> assert false
    in
    let (left, right) = BatList.span (fun (fv,_) -> fv.(feature) <= split_value) bucket in
    Node { value = split_value;
           left = mk_tree (feature - 1) left;
           right = mk_tree (feature - 1) right }
           
let of_list features list =
  let list =
    List.map (fun elt -> (features elt, elt)) list
    |> BatList.sort (fun (fv, _) (fv', _) -> compare_fv fv fv')
  in
  let rec go left fv xs right =
    match right with
    | [] -> List.rev ((fv,xs)::left)
    | (rfv,x)::right ->
      if compare_fv fv rfv = 0 then
        go left fv (x::xs) right
      else
        go ((fv,xs)::left) rfv [x] right
  in
  match list with
  | [] -> empty features
  | (fv,x)::list ->
    { features = features;
      tree = mk_tree (Array.length fv - 1) (go [] fv [x] list) }

let insert elt ft =
  let fv = ft.features elt in
  let nb_features = Array.length fv in
  let rec insert_tree feature = function
    | Leaf bucket -> mk_tree feature (insert_bucket fv elt bucket)
    | Node n ->
      if fv.(feature) <= n.value then
        Node { n with left = insert_tree (feature - 1) n.left }
      else
        Node { n with right = insert_tree (feature - 1) n.right }
  in
  { ft with tree = insert_tree (nb_features - 1) ft.tree }

let enum ft =
  let rec descend tree rest =
    match tree with
    | Leaf bucket -> ([], bucket, rest)
    | Node n -> descend n.left (n.right::rest)
  in
  let rest = ref (descend ft.tree []) in
  let rec next () =
    match !rest with
    | (x::xs, bucket, tree) ->
      rest := (xs, bucket, tree);
      x
    | ([], (fv,xs)::bucket, tree) ->
      rest := (xs, bucket, tree);
      next ()
    | ([], [], (t::ts)) ->
      rest := descend t ts;
      next ()
    | ([], [], []) -> raise BatEnum.No_more_elements
  in
  BatEnum.from next

let features ft elt = ft.features elt

let find_leq fv p ft =
  let find_bucket (fv', xs) =
    if fv_leq fv' fv then
      try Some (BatList.find p xs)
      with Not_found -> None
    else
      None
  in
  let rec find_tree feature = function
    | Leaf xs -> BatList.find_map find_bucket xs
    | Node n ->
      if fv.(feature) <= n.value then
        find_tree (feature - 1) n.left
      else
        try find_tree (feature - 1) n.right
        with Not_found -> find_tree (feature - 1) n.left
  in
  find_tree (Array.length fv - 1) ft.tree

let find_leq_map fv f ft =
  let find_bucket (fv', xs) =
    if fv_leq fv' fv then
      try Some (BatList.find_map f xs)
      with Not_found -> None
    else
      None
  in
  let rec find_tree feature = function
    | Leaf xs -> BatList.find_map find_bucket xs
    | Node n ->
      if fv.(feature) <= n.value then
        find_tree (feature - 1) n.left
      else
        try find_tree (feature - 1) n.right
        with Not_found -> find_tree (feature - 1) n.left
  in
  find_tree (Array.length fv - 1) ft.tree

let remove equal elt ft =
  let fv = ft.features elt in
  let remove_bucket (fv', xs) =
    if compare_fv fv' fv = 0 then
      (fv', List.filter (not % equal elt) xs)
    else
      (fv', xs)
  in
  let rec remove_tree feature = function
    | Leaf xs -> Leaf (BatList.map remove_bucket xs)
    | Node n ->
      if fv.(feature) <= n.value then
        Node { n with left = remove_tree (feature - 1) n.left }
      else
        Node { n with right = remove_tree (feature - 1) n.right }
  in
  { ft with tree = remove_tree (Array.length fv - 1) ft.tree }

let rebalance ft =
  let rec to_bucket = function
    | Leaf xs -> xs
    | Node n ->
      (to_bucket n.left)@(to_bucket n.right)
  in
  let bucket = to_bucket ft.tree in
  match bucket with
  | [] -> empty ft.features
  | (fv,x)::list ->
    { features = ft.features;
      tree = mk_tree (Array.length fv - 1) bucket }
