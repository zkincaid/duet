(** Groebner basis computation using msolve.

    Set the [MSOLVE] environment variable to select an executable
    other than [msolve]. *)

open Polynomial

(* Create a dense vector consisting of the (natural) exponents of a given
   set of variants within a monomial. *)
let mon_to_exp_vec variables monomial =
  List.map (fun variable -> Monomial.power variable monomial) variables

let compare_block variables left right =
  let left_degree = Monomial.total_degree left in
  let right_degree = Monomial.total_degree right in
  if left_degree > right_degree then `Gt
  else if left_degree < right_degree then `Lt
  else
    let diff =
      List.rev_map2
        (-)
        (mon_to_exp_vec variables left)
        (mon_to_exp_vec variables right)
    in
    match List.find_opt ((<>) 0) diff with
    | None -> `Eq
    | Some difference -> if difference < 0 then `Gt else `Lt

let get_mon_order block1 block2 left right =
  let split monomial =
    let in_first, in_second =
      Monomial.enum monomial
      |> BatList.of_enum
      |> List.partition (fun (variable, _) -> List.mem variable block1)
    in
    Monomial.of_enum (BatList.enum in_first),
    Monomial.of_enum (BatList.enum in_second)
  in
  let left1, left2 = split left in
  let right1, right2 = split right in
  match compare_block block1 left1 right1 with
  | (`Lt | `Gt) as result -> result
  | `Eq -> compare_block block2 left2 right2

let shell_quote string =
  Printf.sprintf "'%s'"
    (String.concat "'\\''" (String.split_on_char '\'' string))

let executable () =
  match Sys.getenv_opt "MSOLVE" with
  | Some path -> path
  | None -> "msolve"

let available =
  let available =
    lazy
      (Sys.command
         (Printf.sprintf "command -v %s > /dev/null 2>&1"
            (shell_quote (executable ())))
       = 0)
  in
  fun () -> Lazy.force available

let write_input chan variables polynomials =
  let variable_count = List.length variables in
  let write_monomial exponents =
    let first = ref true in
    List.iteri
      (fun index exponent ->
         if exponent <> 0 then begin
           if not !first then output_char chan '*';
           first := false;
           Printf.fprintf chan "x%d" index;
           if exponent <> 1 then Printf.fprintf chan "^%d" exponent
         end)
      exponents
  in
  let write_polynomial polynomial =
    let denominator = Q.den (QQXs.content polynomial) in
    BatEnum.iteri
      (fun index (coefficient, monomial) ->
         let coefficient =
           Q.num (Q.mul (Q.of_bigint denominator) coefficient)
         in
         let negative = Z.sign coefficient < 0 in
         let magnitude = Z.abs coefficient in
         if index = 0 then (if negative then output_char chan '-')
         else output_char chan (if negative then '-' else '+');
         let exponents = mon_to_exp_vec variables monomial in
         let is_constant = List.for_all ((=) 0) exponents in
         if is_constant || not (Z.equal magnitude Z.one) then begin
           output_string chan (Format.asprintf "%a" Z.pp_print magnitude);
           if not is_constant then output_char chan '*'
         end;
         if not is_constant then write_monomial exponents)
      (QQXs.enum polynomial)
  in
  List.iteri
    (fun index _ ->
       if index <> 0 then output_string chan ", ";
       Printf.fprintf chan "x%d" index)
    variables;
  output_string chan "\n0\n";
  List.iteri
    (fun index polynomial ->
       if index <> 0 then output_string chan ",\n";
       write_polynomial polynomial)
    polynomials;
  if variable_count > 0 then output_char chan '\n'

let read_basis filename variables =
  let chan = open_in filename in
  let contents =
    Fun.protect ~finally:(fun () -> close_in_noerr chan)
      (fun () -> really_input_string chan (in_channel_length chan))
  in
  let uncommented =
    contents
    |> String.split_on_char '\n'
    |> List.filter (fun line ->
           String.length line = 0 || line.[0] <> '#')
    |> String.concat ""
  in
  let left = String.index_opt uncommented '[' in
  let right = String.rindex_opt uncommented ']' in
  let body =
    match left, right with
    | Some left, Some right when left < right ->
      String.sub uncommented (left + 1) (right - left - 1)
    | _ -> failwith "msolve: malformed Groebner basis output"
  in
  let remove_spaces string =
    String.to_seq string
    |> Seq.filter (fun character ->
           character <> ' ' && character <> '\t' && character <> '\r')
    |> String.of_seq
  in
  let parse_term term =
    let factors = String.split_on_char '*' term in
    let coefficient = ref Q.one in
    let exponents = Array.make (List.length variables) 0 in
    List.iter
      (fun factor ->
         if String.length factor > 0 && factor.[0] = 'x' then begin
           let variable, exponent =
             match String.index_opt factor '^' with
             | None -> String.sub factor 1 (String.length factor - 1), 1
             | Some caret ->
               (String.sub factor 1 (caret - 1),
                int_of_string
                  (String.sub factor (caret + 1)
                     (String.length factor - caret - 1)))
           in
           let index = int_of_string variable in
           if index < 0 || index >= Array.length exponents then
             failwith "msolve: variable outside the requested ring";
           exponents.(index) <- exponents.(index) + exponent
         end else
           coefficient := Q.mul !coefficient (Q.of_string factor))
      factors;
    let monomial =
      Array.to_list exponents
      |> List.mapi (fun index exponent -> List.nth variables index, exponent)
      |> List.filter (fun (_, exponent) -> exponent <> 0)
      |> BatList.enum
      |> Monomial.of_enum
    in
    !coefficient, monomial
  in
  let parse_polynomial polynomial =
    let polynomial = remove_spaces polynomial in
    if polynomial = "" || polynomial = "0" then QQXs.zero
    else begin
      let terms = ref [] in
      let start = ref 0 in
      for index = 1 to String.length polynomial - 1 do
        if polynomial.[index] = '+' || polynomial.[index] = '-' then begin
          terms := String.sub polynomial !start (index - !start) :: !terms;
          start := index
        end
      done;
      terms := String.sub polynomial !start
          (String.length polynomial - !start) :: !terms;
      let normalize_sign term =
        if term.[0] = '+' then String.sub term 1 (String.length term - 1)
        else if term.[0] = '-' then
          "-1*" ^ String.sub term 1 (String.length term - 1)
        else term
      in
      !terms
      |> List.rev
      |> List.map (fun term -> parse_term (normalize_sign term))
      |> QQXs.of_list
    end
  in
  if remove_spaces body = "" then []
  else List.map parse_polynomial (String.split_on_char ',' body)

type output_value = Atom of string | List of output_value list

let parse_output string =
  let length = String.length string in
  let position = ref 0 in
  let rec skip () =
    while !position < length &&
          List.mem string.[!position] [' '; '\n'; '\r'; '\t'; ','] do
      incr position
    done
  and value () =
    skip ();
    if !position >= length then failwith "msolve: truncated output";
    match string.[!position] with
    | '[' ->
      incr position;
      let rec elements accumulator =
        skip ();
        if !position >= length then failwith "msolve: unterminated list"
        else if string.[!position] = ']' then begin
          incr position;
          List (List.rev accumulator)
        end else
          elements (value () :: accumulator)
      in
      elements []
    | '\'' ->
      incr position;
      let start = !position in
      while !position < length && string.[!position] <> '\'' do incr position done;
      if !position >= length then failwith "msolve: unterminated string";
      let atom = String.sub string start (!position - start) in
      incr position;
      Atom atom
    | _ ->
      let start = !position in
      while !position < length &&
            not (List.mem string.[!position] [' '; '\n'; '\r'; '\t'; ','; ']']) do
        incr position
      done;
      Atom (String.sub string start (!position - start))
  in
  value ()

let read_parametrization filename =
  let chan = open_in filename in
  let contents =
    Fun.protect ~finally:(fun () -> close_in_noerr chan)
      (fun () -> really_input_string chan (in_channel_length chan))
  in
  let atom = function Atom value -> value | _ -> failwith "msolve: expected atom" in
  let list = function List values -> values | _ -> failwith "msolve: expected list" in
  let rational value = Q.of_string (atom value) in
  let polynomial value =
    match list value with
    | [_degree; coefficients] ->
      list coefficients
      |> List.mapi (fun exponent coefficient -> rational coefficient, exponent)
      |> QQX.of_list
    | _ -> failwith "msolve: malformed encoded polynomial"
  in
  match list (parse_output contents) with
  | [dimension; data] when atom dimension = "0" ->
    begin match list data with
      | [_dimension; _variable_count; _degree; names; linear_form; parametrizations] ->
        let names = List.map atom (list names) in
        let linear_form = List.map rational (list linear_form) in
        begin match list parametrizations with
          | [_count; parametrization] ->
            begin match list parametrization with
              | [minimal_polynomial; denominator; coordinates] ->
                let coordinates =
                  list coordinates
                  |> List.map (fun coordinate ->
                         match list coordinate with
                         | [numerator; scale] -> polynomial numerator, rational scale
                         | _ -> failwith "msolve: malformed coordinate")
                in
                names, linear_form, polynomial minimal_polynomial,
                polynomial denominator, coordinates
              | _ -> failwith "msolve: malformed parametrization"
            end
          | _ -> failwith "msolve: expected one parametrization"
        end
      | _ -> failwith "msolve: malformed parametrization header"
    end
  | dimension :: _ ->
    failwith ("msolve: system does not have dimension zero (dimension " ^
              atom dimension ^ ")")
  | [] -> failwith "msolve: empty output"

let parametrization variables polynomials =
  let nonzero =
    List.filter (fun polynomial -> not (QQXs.is_zero polynomial)) polynomials
  in
  let input = Filename.temp_file "srk-msolve-" ".ms" in
  let output = Filename.temp_file "srk-msolve-" ".out" in
  Fun.protect
    ~finally:(fun () ->
        (try Sys.remove input with Sys_error _ -> ());
        (try Sys.remove output with Sys_error _ -> ()))
    (fun () ->
       let chan = open_out input in
       Fun.protect ~finally:(fun () -> close_out_noerr chan)
         (fun () -> write_input chan variables nonzero);
       let command =
         Printf.sprintf "%s -v 0 -P 2 -f %s -o %s"
           (shell_quote (executable ())) (shell_quote input) (shell_quote output)
       in
       let status = Sys.command command in
       if status <> 0 then
         failwith (Printf.sprintf "msolve exited with status %d" status);
       let names, linear_form, m, denominator, coordinates =
         read_parametrization output
       in
       let modulo p = snd (QQX.qr p m) in
       (* msolve gives each coordinate as a numerator/scale pair, representing
          -(numerator / scale) / denominator modulo m. *)
       let denominator_inverse =
         let gcd, inverse, _ = QQX.gcdext denominator m in
         if QQX.order gcd <> 0 then
           failwith "msolve: parametrization denominator is not invertible";
         inverse
       in
       let value (numerator, scale) =
         QQX.mul numerator denominator_inverse
         |> QQX.scalar_mul (Q.neg (Q.inv scale))
         |> modulo
       in
       let values = List.map value coordinates in
       (* msolve may omit the coordinate of its last variable (which may be a
          variable that it introduced); it is determined by the linear form
          t = sum_i l_i x_i. *)
       let values =
         let arity = List.length names in
         if List.length values = arity then values
         else if List.length values + 1 = arity
              && List.length linear_form = arity then
           match List.rev linear_form with
           | last :: rest when not (Q.equal last Q.zero) ->
             let sum =
               List.fold_left2
                 (fun sum coefficient value ->
                    QQX.add sum (QQX.scalar_mul coefficient value))
                 QQX.zero
                 (List.rev rest)
                 values
             in
             values
             @ [modulo (QQX.scalar_mul (Q.inv last) (QQX.sub QQX.identity sum))]
           | _ -> failwith "msolve: cannot reconstruct the last coordinate"
         else failwith "msolve: inconsistent parametrization arity"
       in
       let named_values = List.combine names values in
       let values =
         List.mapi
           (fun index _ ->
              let name = Printf.sprintf "x%d" index in
              match List.assoc_opt name named_values with
              | Some value -> value
              | None -> failwith ("msolve: missing coordinate " ^ name))
           variables
       in
       m, values)

let grobner_basis block1 block2 polynomials =
  if block1 = [] then invalid_arg "Msolve.grobner_basis: empty first block";
  if block2 <> [] then
    invalid_arg "Msolve.grobner_basis: block orders are not supported";
  let variables = block1 @ block2 in
  let nonzero = List.filter (fun polynomial -> not (QQXs.is_zero polynomial)) polynomials in
  if nonzero = [] then [QQXs.zero]
  else begin
    let input = Filename.temp_file "srk-msolve-" ".ms" in
    let output = Filename.temp_file "srk-msolve-" ".out" in
    Fun.protect
      ~finally:(fun () ->
          (try Sys.remove input with Sys_error _ -> ());
          (try Sys.remove output with Sys_error _ -> ()))
      (fun () ->
         let chan = open_out input in
         Fun.protect ~finally:(fun () -> close_out_noerr chan)
           (fun () -> write_input chan variables nonzero);
         let command =
           Printf.sprintf "%s -v 0 -g 2 -f %s -o %s"
             (shell_quote (executable ()))
             (shell_quote input) (shell_quote output)
         in
         let status = Sys.command command in
         if status <> 0 then
           failwith (Printf.sprintf "msolve exited with status %d" status);
         read_basis output variables)
  end

let eliminate block1 block2 polynomials =
  if block1 = [] then invalid_arg "Msolve.eliminate: empty elimination block";
  if block2 = [] then
    let eliminated = SrkUtil.Int.Set.of_list block1 in
    grobner_basis block1 [] polynomials
    |> List.filter
         (fun polynomial ->
            SrkUtil.Int.Set.disjoint
              (QQXs.dimensions polynomial)
              eliminated)
  else
    let variables = block1 @ block2 in
    let nonzero =
      List.filter (fun polynomial -> not (QQXs.is_zero polynomial)) polynomials
    in
    if nonzero = [] then [QQXs.zero]
    else
      let basis =
        let input = Filename.temp_file "srk-msolve-" ".ms" in
        let output = Filename.temp_file "srk-msolve-" ".out" in
        Fun.protect
          ~finally:(fun () ->
              (try Sys.remove input with Sys_error _ -> ());
              (try Sys.remove output with Sys_error _ -> ()))
          (fun () ->
             let chan = open_out input in
             Fun.protect ~finally:(fun () -> close_out_noerr chan)
               (fun () -> write_input chan variables nonzero);
             let command =
               Printf.sprintf "%s -v 0 -g 2 -e %d -f %s -o %s"
                 (shell_quote (executable ())) (List.length block1)
                 (shell_quote input) (shell_quote output)
             in
             let status = Sys.command command in
             if status <> 0 then
               failwith (Printf.sprintf "msolve exited with status %d" status);
             read_basis output variables)
      in
      let eliminated = SrkUtil.Int.Set.of_list block1 in
      List.filter
        (fun polynomial ->
           SrkUtil.Int.Set.disjoint
             (QQXs.dimensions polynomial)
             eliminated)
        basis
