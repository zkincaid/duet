open BatPervasives

include Log.Make(struct let name = "srk.featureTree" end)
    
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
    feature : int;
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
      | _ ->
        (fv',elts)::(insert_bucket fv elt xs)
    end
  | [] -> [fv,[elt]]

let rec mk_tree nb_features bucket =
  if List.length bucket <= bucket_size then
    Leaf (List.sort (fun (fv, _) (fv', _) -> compare_fv fv fv') bucket)
  else
    let (feature,value) =
      let len = List.length bucket in
      let ft = fst (List.nth bucket (Random.int len)) in
      let leq = Array.make nb_features 0 in
      bucket |> List.iter (fun (x, _) ->
          for i = 0 to nb_features - 1; do
            if x.(i) <= ft.(i) then
              leq.(i) <- leq.(i) + 1
          done);
      let mid = (len+1) / 2 in
      let feature = ref 0 in
      let size = ref (abs (mid - leq.(0))) in
      for i = 0 to nb_features - 1; do
        let size' = abs (mid - leq.(i)) in
        if (size' < (!size) || (size' = (!size) && Random.bool ())) then begin
          feature := i;
          size := size'
        end
      done;
      (!feature, ft.(!feature))
    in
    let (left, right) =
      List.partition (fun (f,_) -> f.(feature) <= value) bucket
    in
    Node { value = value;
           feature = feature;
           left = mk_tree nb_features left;
           right = mk_tree nb_features right }

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
      tree = mk_tree (Array.length fv) (go [] fv [x] list) }

let insert elt ft =
  let fv = ft.features elt in
  let nb_features = Array.length fv in
  let rec insert_tree = function
    | Leaf bucket -> mk_tree nb_features (insert_bucket fv elt bucket)
    | Node n ->
      if fv.(n.feature) <= n.value then
        Node { n with left = insert_tree n.left }
      else
        Node { n with right = insert_tree n.right }
  in
  { ft with tree = insert_tree ft.tree }

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
    | ([], (_,xs)::bucket, tree) ->
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
  let rec find f = function
    | [] -> None
    | (x::xs) -> if f x then Some x else find f xs
  in
  let find_bucket (fv', xs) =
    if fv_leq fv' fv then
      find p xs
    else
      None
  in
  let rec find_tree = function
    | Leaf xs -> BatList.find_map find_bucket xs
    | Node n ->
      if fv.(n.feature) <= n.value then
        find_tree n.left
      else
        try find_tree n.left
        with Not_found -> find_tree n.right
  in
  find_tree ft.tree

let find_leq_map fv f ft =
  let find_bucket (fv', xs) =
    if fv_leq fv' fv then
      try Some (BatList.find_map f xs)
      with Not_found -> None
    else
      None
  in
  let rec find_tree = function
    | Leaf xs -> BatList.find_map find_bucket xs
    | Node n ->
      if fv.(n.feature) <= n.value then
        find_tree n.left
      else
        try find_tree n.right
        with Not_found -> find_tree n.left
  in
  find_tree ft.tree

let remove equal elt ft =
  let fv = ft.features elt in
  let remove_bucket (fv', xs) =
    if compare_fv fv' fv = 0 then
      (fv', List.filter (not % equal elt) xs)
    else
      (fv', xs)
  in
  let rec remove_tree = function
    | Leaf xs -> Leaf (BatList.map remove_bucket xs)
    | Node n ->
      if fv.(n.feature) <= n.value then
        Node { n with left = remove_tree n.left }
      else
        Node { n with right = remove_tree n.right }
  in
  { ft with tree = remove_tree ft.tree }

let rebalance ft =
  let bucket = ref [] in
  let rec to_bucket = function
    | Leaf xs ->
      bucket := xs@(!bucket);
    | Node n ->
      to_bucket n.left; to_bucket n.right
  in
  to_bucket ft.tree;
  match !bucket with
  | [] -> empty ft.features
  | (fv,_)::_ ->
    { features = ft.features;
      tree = mk_tree (Array.length fv) (!bucket) }
