module A = BatDynArray

type 'a link =
  { mutable parent : int;
    mutable weight : 'a }

type node = int

type 'a t =
  { links : ('a link option) A.t;
    one : 'a;
    mul : 'a -> 'a -> 'a }

let create ~mul ~one =
  { links = A.make 32; one; mul }

let rec compress forest i =
  match A.get forest.links i with
  | None -> (i, forest.one)
  | Some link ->
     let (root, weight) = compress forest link.parent in
     if root != link.parent then begin
         link.parent <- root;
         link.weight <- forest.mul link.weight weight
       end;
     (link.parent, link.weight)

let root forest =
  let pos = A.length forest.links in
  A.add forest.links None;
  pos

let find forest i = fst (compress forest i)

let eval forest i = snd (compress forest i)

let link forest ~child weight ~parent =
  assert (child != parent);
  if A.get forest.links child != None then
    invalid_arg "Cannot link: child already has a parent";
  A.set forest.links child (Some { parent; weight })
