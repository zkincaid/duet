open Batteries

let default_sep formatter () = Format.fprintf formatter ",@ "
let pp_print_enum_nobox ?(pp_sep=default_sep) pp_elt formatter enum =
  match BatEnum.get enum with
  | None   -> ()
  | Some x -> begin
      pp_elt formatter x;
      BatEnum.iter (fun elt ->
          pp_sep formatter ();
          pp_elt formatter elt
        ) enum;
    end
let pp_print_enum ?(indent=2) ?(pp_sep=default_sep) pp_elt formatter enum =
  Format.pp_open_hovbox formatter indent;
  pp_print_enum_nobox ~pp_sep pp_elt formatter enum;
  Format.pp_close_box formatter ()

let cartesian_product e1 e2 =
  let e2c = ref (BatEnum.clone e2) in
  let go () =
    match BatEnum.peek e1 with
    | None -> raise BatEnum.No_more_elements
    | Some x -> begin match BatEnum.get (!e2c) with
        | Some y -> (x, y)
        | None -> begin
            BatEnum.junk e1;
            e2c := BatEnum.clone e2;
            match BatEnum.peek e1, BatEnum.get (!e2c) with
            | Some x, Some y -> (x, y)
            | _, _ -> raise BatEnum.No_more_elements
          end
      end
  in
  BatEnum.from go

let rec tuples = function
  | [x] -> x /@ (fun elt -> [elt])
  | (x::xs) ->
    cartesian_product x (tuples xs) /@ (fun (x,y) -> x::y)
  | [] -> BatEnum.singleton []

let adjacent_pairs enum =
  let go () = match BatEnum.get enum, BatEnum.peek enum with
    | Some x, Some y -> (x, y)
    | _, _ -> raise BatEnum.No_more_elements
  in
  BatEnum.from go

let distinct_pairs enum =
  match BatEnum.get enum with
  | None -> BatEnum.empty ()
  | Some first ->
    let rest = ref (BatEnum.clone enum) in
    let cur = ref first in
    let rec go () =
      match BatEnum.get (!rest) with
      | None -> begin
          cur := BatEnum.get_exn enum;
          rest := BatEnum.clone enum;
          go ()
        end
      | Some elt -> (!cur, elt)
    in
    BatEnum.from go
