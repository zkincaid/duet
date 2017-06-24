module A = BatDynArray

(* Search for an index in a sorted array *)
let search ?compare:(compare = Pervasives.compare) v array =
  let rec go min max =
    if max < min then raise Not_found
    else begin
      let mid = min + ((max - min) / 2) in
      let cmp = compare v (A.get array mid) in
      if cmp < 0 then go min (mid - 1)
      else if cmp > 0 then go (mid + 1) max
      else mid
    end
  in
  go 0 (A.length array - 1)

(* Merge two (sorted) arrays *)
let merge_array ?compare:(compare = Pervasives.compare) a b =
  let alen = Array.length a in
  let blen = Array.length b in
  (* count the size of the intersection of a and b *)
  let rec common i j acc =
    if i == alen || j == blen then acc else begin
      let cmp = compare a.(i) b.(j) in
      if cmp < 0 then common (i + 1) j acc
      else if cmp > 0 then common i (j + 1) acc
      else common (i + 1) (j + 1) (acc + 1)
    end
  in
  let clen = alen + blen - (common 0 0 0) in
  let c = Array.make clen (Obj.magic ()) in
  let rec go i j k =
    if k < clen then begin
      if i == alen then (c.(k) <- b.(j); go i (j + 1) (k + 1))
      else if j == blen then (c.(k) <- a.(i); go (i + 1) j (k + 1))
      else begin
        let cmp = compare a.(i) b.(j) in
        if cmp < 0 then (c.(k) <- a.(i); go (i + 1) j (k + 1))
        else if cmp > 0 then (c.(k) <- b.(j); go i (j + 1) (k + 1))
        else (c.(k) <- a.(i); go (i + 1) (j + 1) (k + 1))
      end
    end
  in
  go 0 0 0;
  c

let rec exp mul one p n =
  if n = 0 then one
  else if n = 1 then p
  else begin
    let q = exp mul one p (n / 2) in
    let q_squared = mul q q in
    if n mod 2 = 0 then q_squared
    else mul q q_squared
  end
