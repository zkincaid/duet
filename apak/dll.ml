type 'a dll_node = { mutable prev : 'a dll_entry;
                     mutable next : 'a dll_entry;
                     mutable elt  : 'a }
and 'a dll_entry =
  | DllEmpty
  | DllNode of 'a dll_node

type 'a t =
  { mutable front : 'a dll_entry;
    mutable back  : 'a dll_entry;
    mutable size  : int }

let create () =
  { front = DllEmpty;
    back = DllEmpty;
    size = 0 }

let size dll = dll.size

let singleton elt = DllNode { prev = DllEmpty;
                              next = DllEmpty;
                              elt  = elt }

let set_next x y =
  begin match x with
    | DllNode x -> (x.next <- y)
    | DllEmpty -> ()
  end;
  begin match y with
    | DllNode y -> (y.prev <- x)
    | DllEmpty -> ()
  end

let is_empty dll = size dll = 0

let push elt dll =
  let nr = { prev = DllEmpty;
             next = DllEmpty;
             elt  = elt }
  in
  let node = DllNode nr in
  set_next node dll.front;
  dll.front <- node;
  if is_empty dll then dll.back <- node;
  dll.size <- dll.size + 1;
  nr

let top dll = match dll.front with
  | DllNode n -> n.elt
  | DllEmpty -> raise Not_found

let elt node = node.elt

let concat a b =
  if is_empty a then b
  else if is_empty b then a
  else begin
    set_next a.back b.front;
    { front = a.front;
      back = b.back;
      size = a.size + b.size }
  end

let iter f dll =
  let rec go = function
    | DllNode n -> f n.elt; go n.next
    | DllEmpty -> ()
  in
  go dll.front

let delete dll node =
  dll.size <- dll.size - 1;
  set_next node.prev node.next;
  match dll.front, dll.back with
  | (DllNode fn, DllNode bn) ->
    if fn == node then dll.front <- node.next;
    if bn == node then dll.back <- node.prev
  | _ -> invalid_arg "Dll.delete on an empty list"
