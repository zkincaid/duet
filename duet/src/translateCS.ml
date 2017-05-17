open InterIR

(* References *)
let procs_lst = ref []
let glos = ref []
let main = ref {fname = " main "; fargs = []; flocs = []; fbody = (Array.of_list []); fret = None}
let prev_call = ref false
let was_assert = ref false
let cur_locs = ref []
let cur_args = ref []
let temp_func = ref {fname = ""; fargs = []; flocs = []; fbody = (Array.of_list [{bpreds = [-1]; binsts = []; btype = Branch([1]); bcond = None}; {bpreds = [0]; binsts = []; btype = Return(None); bcond = None}]); fret = None}
let node_id = ref 0
let blk_preds = ref []



  (* Determine the type of the variable based on the type name *)
  let get_type t_name =
    if ((String.compare t_name "int") = 0) or ((String.compare t_name "type:[c:integer] int") = 0) then begin
      Int(4)
    end
    else if ((String.compare t_name "void") = 0) or ((String.compare t_name "type:[c:void] void") = 0) then begin
      Void
    end
    else if ((String.compare t_name "long long") = 0) or ((String.compare t_name "type:[c:integer] long long") = 0) then begin
      Int(8)
    end
    else if ((String.compare t_name "unsigned char") = 0) or ((String.compare t_name "type:[c:integer] unsigned char") = 0) then begin
      Int(1)
    end
    else begin
      Unknown
    end


  let parse_dot d_ast =
    let fields = ((Swig.invoke d_ast) "fields" (Swig.C_void)) in
    let field = ((Swig.invoke fields) "[]" (Swig.C_int 1)) in
    let field_t = ((Swig.invoke field) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
    let field_str = Swig.get_string ((Swig.invoke field_t) "as_str" (Swig.C_void)) in
    (*Printf.printf "field_stirng: %s\n" field_str;*)
    let strct = ((Swig.invoke fields) "[]" (Swig.C_int 0)) in
    let strct_ast = ((Swig.invoke strct) "as_ast" (Swig.C_void)) in
    let strct_fields = ((Swig.invoke strct_ast) "fields" (Swig.C_void)) in
    let strct_n = ((Swig.invoke strct_fields) "[]" (Swig.C_int 0)) in
    let strct_name = ((Swig.invoke strct_n) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
    let strct_str = Swig.get_string ((Swig.invoke strct_name) "as_str" (Swig.C_void)) in
    (*Printf.printf "strct_str: %s\n" strct_str;*)
    let field_name = (if (String.compare field_str "ub") = 0 then begin "upper" end else begin "lower" end) in
    let strct_field_name = strct_str ^ "_" ^ field_name in
    (*Printf.printf "strc_field_name: %s\n" strct_field_name;*)
    (if not (List.mem (Var(strct_field_name,Int(4))) !cur_args) then begin
      (if not (List.mem (Var(strct_field_name,Int(4))) !glos) then begin
        (if not (List.mem (Var(strct_field_name,Int(4))) !cur_locs) then begin
         cur_locs := (Var(strct_field_name,Int(4))) :: !cur_locs end)
      end)
    end);
    LVal(Var(strct_field_name,Int(4)))

  (* Parse a variable and return the integer or variable representation *)
  let rec parse_var f =
  let f_ast = ((Swig.invoke f) "as_ast" (Swig.C_void)) in
  let f_class = ((Swig.invoke f_ast) "get_class" (Swig.C_void)) in
  let f_class_super = ((Swig.invoke f_class) "superclass" (Swig.C_void)) in
  let f_class_super_str = Swig.get_string ((Swig.invoke f_class_super) "as_string" (Swig.C_void)) in
  let f_class_str = Swig.get_string ((Swig.invoke f_class) "as_string" (Swig.C_void)) in
  let f_class_super_super = ((Swig.invoke f_class_super) "superclass" (Swig.C_void)) in
  let f_class_super_super_str = Swig.get_string ((Swig.invoke f_class_super_super) "as_string" (Swig.C_void)) in
  if (String.compare f_class_str "c:integer-value-32") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      LVal(Constant(int_val,4))
  end
  else if (String.compare f_class_str "c:integer-value-64") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int64" (Swig.C_void)) in
      LVal(Constant(int_val,8))
  end
  else if (String.compare f_class_str "c:integer-value-128") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      LVal(Constant(int_val,16))
  end
  else if (String.compare f_class_str "c:uinteger-value-32") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      LVal(Constant(int_val,4))
  end
  else if (String.compare f_class_str "c:uinteger-value-64") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      LVal(Constant(int_val,8))
  end
  else if (String.compare f_class_str "c:integer-value-128") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      LVal(Constant(int_val,16))
  end
  else if (String.compare f_class_super_super_str "c:literal") = 0 then begin
    Havoc
  end
  (* It is a variable *)
  else if (String.compare f_class_str "c:variable") = 0 then begin
    let sym_type = ((Swig.invoke f_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
    let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
    let ty = get_type sym_type_str in
    let name = ((Swig.invoke f_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
    let name_str = (Swig.get_string ((Swig.invoke name) "as_str" (Swig.C_void))) in
    if (String.compare name_str "nondetI") = 0 then begin
      Havoc
    end
    else if (String.compare name_str "nondetC") = 0 then begin
      Havoc
    end
    else if (String.compare name_str "nondetZ") = 0 then begin
      Havoc
    end
    else begin
    (if not (List.mem (Var(name_str,ty)) !cur_args) then begin
    (* Add static class variables to global list, if needed *)
    (if not (List.mem (Var(name_str,ty)) !glos) then begin
      (if not (List.mem (Var(name_str,ty)) !cur_locs) then begin
         cur_locs := (Var(name_str,ty)) :: !cur_locs end)
      end)
    end);
    LVal(Var(name_str,ty))
  end
  end
  else if (String.compare f_class_str "c:dot") = 0 then begin
    parse_dot f_ast end
  (* It is a unary - value, get the variable value*)
  else if (String.compare f_class_super_str "c:arithmetic") = 0 then begin
    if (String.compare f_class_str "c:unary-") = 0 then begin
      let fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
      let neg_field = ((Swig.invoke fields) "[]" (Swig.C_int 0)) in
      let x = parse_var neg_field in
    UNeg(x)
      end
    else begin
      LVal(Constant(0,4))
    end
  end
  else begin
    LVal(Constant(0,4))
  end

  let parse_length f =
    let f_ast = ((Swig.invoke f) "as_ast" (Swig.C_void)) in
    let f_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let f_var = ((Swig.invoke f_fields) "[]" (Swig.C_int 0)) in
    let f_var_ast = ((Swig.invoke f_var) "as_ast" (Swig.C_void)) in
    let name = ((Swig.invoke f_var_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
    let name_str = (Swig.get_string ((Swig.invoke name) "as_str" (Swig.C_void))) in
    let name_length_str = name_str ^ "_length" in
    let sym_type = ((Swig.invoke f_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
    let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
    let ty = get_type sym_type_str in
    (if not (List.mem (Var(name_length_str,ty)) !cur_args) then begin
      (if not (List.mem (Var(name_length_str,ty)) !glos) then begin
        (if not (List.mem (Var(name_length_str,ty)) !cur_locs) then begin
         cur_locs := (Var(name_length_str,ty)) :: !cur_locs end)
      end)
    end);
    LVal(Var(name_length_str,ty))

  (*A helper function to recurisvely parse lsums*)
  let rec parse_lsum f : lsum option =
  let f_string = Swig.get_string ((Swig.invoke f) "as_string" (Swig.C_void)) in
  let f_ast = ((Swig.invoke f) "as_ast" (Swig.C_void)) in
  let f_class = ((Swig.invoke f_ast) "get_class" (Swig.C_void)) in
  let f_class_super = ((Swig.invoke f_class) "superclass" (Swig.C_void)) in
  let f_class_super_str = Swig.get_string ((Swig.invoke f_class_super) "as_string" (Swig.C_void)) in
  let f_class_str = Swig.get_string ((Swig.invoke f_class) "as_string" (Swig.C_void)) in
  let f_class_super_super = ((Swig.invoke f_class_super) "superclass" (Swig.C_void)) in
  let f_class_super_super_str = Swig.get_string ((Swig.invoke f_class_super_super) "as_string" (Swig.C_void)) in
  (* The lsum is an integer, return a C4B integer value *)
  if (String.compare f_class_str "c:integer-value-32") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      Some(LVal(Constant(int_val,4)))
  end
  else if (String.compare f_class_str "c:integer-value-64") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      Some(LVal(Constant(int_val,8)))
  end
  else if (String.compare f_class_str "c:integer-value-128") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      Some(LVal(Constant(int_val,16)))
  end
  else if (String.compare f_class_str "c:uinteger-value-32") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      Some(LVal(Constant(int_val,4)))
  end
  else if (String.compare f_class_str "c:uinteger-value-64") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      Some(LVal(Constant(int_val,8)))
  end
  else if (String.compare f_class_str "c:integer-value-128") = 0 then begin
    let int_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let i_fld = ((Swig.invoke int_fields) "[]" (Swig.C_int 0)) in
    let int_val = Swig.get_int ((Swig.invoke i_fld) "as_int32" (Swig.C_void)) in
      Some(LVal(Constant(int_val,16)))
  end
  else if (String.compare f_class_super_super_str "c:literal") = 0 then begin
     Some(Havoc)
  end
  else if (String.compare f_class_str "c:variable") = 0 then begin
    let name = ((Swig.invoke f_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
    let name_str = (Swig.get_string ((Swig.invoke name) "as_str" (Swig.C_void))) in
    let sym_type = ((Swig.invoke f_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
    let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
    let ty = get_type sym_type_str in
    (* If the variable is not an argument variable *)
    (if not (List.mem (Var(name_str,ty)) !cur_args) then begin
      (* If the variable is not a global and not in the local list, add it to the local list *)
      (if not (List.mem (Var(name_str,ty)) !glos) then begin
        (if not (List.mem (Var(name_str,ty)) !cur_locs) then begin
          cur_locs := Var(name_str,ty) :: !cur_locs
        end)
      end)
    end);
    Some(LVal(Var(name_str,ty)))
   end
  (* The LValue is an arightmetic operation, so parse it again, if it's a unary -, add the negation and parse the LValue *)
   else if (String.compare f_class_super_str "c:arithmetic") = 0 then begin
     if (String.compare f_class_str "c:unary-") = 0 then begin
       let fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
       let neg_field = parse_lsum ((Swig.invoke fields) "[]" (Swig.C_int 0)) in
       match neg_field with
         Some(n) -> Some(UNeg(n))
       | None -> None
     end
    else begin
    (* It's a binary op of two Lsums, so parse it if possible - otherwise return a nondet value *)
    let sub_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let left = parse_lsum ((Swig.invoke sub_fields) "[]" (Swig.C_int 0)) in
    match left with
      None -> None
    | Some(lft) -> (
      let right = parse_lsum ((Swig.invoke sub_fields) "[]" (Swig.C_int 1)) in
      match right with
        None -> None
        | Some(rgt) -> (
          let possible_op = String.sub f_class_str 2 1 in
          (match possible_op with
            "+" -> Some(LExpr(lft,Add,rgt))
          | "-" -> Some(LExpr(lft,Sub,rgt))
          | "*" -> Some(LExpr(lft,Mult,rgt))
          | "/" -> Some(LExpr(lft,Div,rgt))
          | "%" -> Some(LExpr(lft,Rem,rgt)))
        )
      )
    end
  end
  else if (String.compare f_class_super_str "c:bitwise") = 0 then begin
    let sub_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let left = parse_lsum ((Swig.invoke sub_fields) "[]" (Swig.C_int 0)) in
    let possible_op = String.sub f_class_str 2 1 in
    match left with
      None -> None
    | Some(lft) -> (
      match possible_op with
       "~" -> Some(LNeg(lft))
      | _ -> (
        let right = parse_lsum ((Swig.invoke sub_fields) "[]" (Swig.C_int 1)) in
        match right with
          None -> None
          | Some(rgt) -> (
            (match possible_op with
              "&" -> Some(LExpr(lft,BAnd,rgt))
            | "<" -> Some(LExpr(lft,LShift,rgt))
            | ">" -> Some(LExpr(lft,RShift,rgt))
            | "^" -> Some(LExpr(lft,BXor,rgt))
            | "b" -> Some(LExpr(lft,BOr,rgt))
            )
          )
        )
      )
  end
  else begin
    None
  end

  let parse_array_access f =
    let f_ast = ((Swig.invoke f) "as_ast" (Swig.C_void)) in
    let f_string = Swig.get_string ((Swig.invoke f_ast) "as_string" (Swig.C_void)) in
    let f_fields = ((Swig.invoke f_ast) "fields" (Swig.C_void)) in
    let f_sub = ((Swig.invoke f_fields) "[]" (Swig.C_int 0)) in
    let f_sub_ast = ((Swig.invoke f_sub) "as_ast" (Swig.C_void)) in
    let f_string2 = Swig.get_string ((Swig.invoke f_sub_ast) "as_string" (Swig.C_void)) in
    let f_sub_ast_type = ((Swig.invoke f_sub_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
    let f_sub_type_string = Swig.get_string ((Swig.invoke f_sub_ast_type) "as_string" (Swig.C_void)) in
    if (String.compare f_sub_type_string "type:[c:pointer] struct abs_interval*") = 0 then
    begin
      let name_u = f_string2^"_upper" in
      let name_l = f_string2^"_lower" in
      (if not (List.mem (Var(name_u,Int(4))) !cur_args) then begin
                (if not (List.mem (Var(name_u,Int(4))) !glos) then begin
                  (if not (List.mem (Var(name_u,Int(4))) !cur_locs) then begin
                    cur_locs := Var(name_u,Int(4)) :: !cur_locs end)
                end)
              end);
      (if not (List.mem (Var(name_l,Int(4))) !cur_args) then begin
                (if not (List.mem (Var(name_l,Int(4))) !glos) then begin
                  (if not (List.mem (Var(name_l,Int(4))) !cur_locs) then begin
                    cur_locs := Var(name_l,Int(4)) :: !cur_locs end)
                end)
              end);
      LVal(Var(f_string2,Int(4)))
    end
    else begin
    let f_sub_fields = ((Swig.invoke f_sub_ast) "fields" (Swig.C_void)) in
    let f_var_field = ((Swig.invoke f_sub_fields) "[]" (Swig.C_int 0)) in
    let f_var_ast = ((Swig.invoke f_var_field) "as_ast" (Swig.C_void)) in
    let f_var_fields = ((Swig.invoke f_var_ast) "fields" (Swig.C_void)) in
    let f_ptr = ((Swig.invoke f_var_fields) "[]" (Swig.C_int 0)) in
    let f_ptr_ast = ((Swig.invoke f_ptr) "as_ast" (Swig.C_void)) in
    let f_ptr_fields = ((Swig.invoke f_ptr_ast) "fields" (Swig.C_void)) in
    let f_name = ((Swig.invoke f_ptr_fields) "[]" (Swig.C_int 0)) in
    let f_name_ast = ((Swig.invoke f_name) "as_ast" (Swig.C_void)) in
    let f_name_ord = ((Swig.invoke f_name_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
    let f_name_str = Swig.get_string ((Swig.invoke f_name_ord) "as_str" (Swig.C_void)) in
    let name_array_str = f_name_str ^ "_array" in
    let p_fields = ((Swig.invoke f_name_ast) "fields" (Swig.C_void)) in
    let ty_f = ((Swig.invoke p_fields) "[]" (Swig.C_int 1)) in
    let array_t = ((Swig.invoke ty_f) "as_ast" (Swig.C_void)) in
    let tp_fields = ((Swig.invoke array_t) "fields" (Swig.C_void)) in
    let typ = ((Swig.invoke tp_fields) "[]" (Swig.C_int 1)) in
    let typ_ast = ((Swig.invoke typ) "as_ast" (Swig.C_void)) in
    let typ_fields = ((Swig.invoke typ_ast) "fields" (Swig.C_void)) in
    let ty_ft = ((Swig.invoke typ_fields) "[]" (Swig.C_int 1)) in
    let l_ast = ((Swig.invoke ty_ft) "as_ast" (Swig.C_void)) in
    let ptr_type = ((Swig.invoke l_ast) "[]" (Cs._ast_ordinal_NC_POINTED_TO(Swig.C_void))) in
    let ptd_to = ((Swig.invoke ptr_type) "as_ast" (Swig.C_void)) in
    let type_string = Swig.get_string ((Swig.invoke ptd_to) "as_string" (Swig.C_void)) in
    let ty = get_type type_string in
    let f_index_field = ((Swig.invoke f_sub_fields) "[]" (Swig.C_int 1)) in
    let f_index_ast = ((Swig.invoke f_index_field) "as_ast" (Swig.C_void)) in
    let f_index_val_fields = ((Swig.invoke f_index_ast) "fields" (Swig.C_void)) in
    let f_index_val = ((Swig.invoke f_index_val_fields) "[]" (Swig.C_int 0)) in
    let int_val = parse_lsum f_index_field in
    let rh = (match int_val with
      Some(x) -> x
      | _ -> LVal(Constant(0,4))) in
    (if not (List.mem (Var(name_array_str,Array(ty))) !cur_args) then begin
      (if not (List.mem (Var(name_array_str,Array(ty))) !glos) then begin
        (if not (List.mem (Var(name_array_str,Array(ty))) !cur_locs) then begin
         cur_locs := (Var(name_array_str,Array(ty))) :: !cur_locs end)
      end)
    end);
    ArrayAccess(Var(name_array_str,Array(ty)),rh)
    end



  (* Flip the conditional value based on the string representation *)
  let get_conditional str flp =
  if (String.contains str '>') then begin
    if (String.contains str '=') then begin
      if flp then LT else GTE
    end
    else begin
      if flp then LTE else GT
    end
  end
  else if (String.contains str '<') then begin
    if (String.contains str '=') then begin
      if flp then GT else LTE
    end
    else begin
      if flp then GTE else LT
    end
  end
  else if (String.contains str '!') then begin
    if flp then EQ else NE
  end
  else begin
    if flp then NE else EQ
  end;;

  (*Returns a string representing the arguments to a function call*)
  let rec get_param_vars size loc actuals_in p_str =
  if (size == loc) then []
  else begin
    let param = ((Swig.invoke actuals_in) "[]" (Swig.C_int loc)) in
    let p_ast = ((Swig.invoke param) "get_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
    let p_field = (Swig.invoke ((Swig.invoke p_ast) "fields" (Swig.C_void))) "[]" (Swig.C_int 1) in
    let param_str = Swig.get_string ((Swig.invoke p_field) "as_string" (Swig.C_void)) in
    let sym_type = ((Swig.invoke p_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
    let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
    if (String.length sym_type_str > 33) then begin
      let sub_type = String.sub sym_type_str 24 10 in
      if ((String.compare sub_type "java_array") = 0) then begin
        let name = ((Swig.invoke p_field) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
        let name_str = Swig.get_string ((Swig.invoke name) "as_str" (Swig.C_void)) in
        let name_length = name_str ^ "_length" in
        let name_array = name_str ^ "_array" in
        let p_fields = ((Swig.invoke p_ast) "fields" (Swig.C_void)) in
        let typ = ((Swig.invoke p_fields) "[]" (Swig.C_int 1)) in
        let typ_ast = ((Swig.invoke typ) "as_ast" (Swig.C_void)) in
        let typ_fields = ((Swig.invoke typ_ast) "fields" (Swig.C_void)) in
        let ty_f = ((Swig.invoke typ_fields) "[]" (Swig.C_int 1)) in
        let array_t = ((Swig.invoke ty_f) "as_ast" (Swig.C_void)) in
        let array_t_fields = ((Swig.invoke array_t) "fields" (Swig.C_void)) in
        let array_type = ((Swig.invoke array_t_fields) "[]" (Swig.C_int 1)) in
        let ptr_t = ((Swig.invoke array_type) "as_ast" (Swig.C_void)) in
        let ptr_t_fields = ((Swig.invoke ptr_t) "fields" (Swig.C_void)) in
        let ptr_t_type = ((Swig.invoke ptr_t_fields) "[]" (Swig.C_int 1)) in
        let ptr_t_ast = ((Swig.invoke ptr_t_type) "as_ast" (Swig.C_void)) in
        let ptr_type = ((Swig.invoke ptr_t_ast) "[]" (Cs._ast_ordinal_NC_POINTED_TO(Swig.C_void))) in
        let ptd_to = ((Swig.invoke ptr_type) "as_ast" (Swig.C_void)) in
        let type_string = Swig.get_string ((Swig.invoke ptd_to) "as_string" (Swig.C_void)) in
        let ty = get_type type_string in
        let l_var = LVal(Var(name_length,Int(4))) in
        let a_var = LVal(Var(name_array,Array(ty))) in
        [l_var;a_var] @ (get_param_vars size (loc + 1) actuals_in p_str)
      end
      else if (String.length sym_type_str > 35) then begin
        let sub_type_a = String.sub sym_type_str 24 12 in
        (*Printf.printf "psub_str: %s\n" sub_type_a;*)
        if ((String.compare sub_type_a "abs_interval") = 0) then begin
          try
            let name = ((Swig.invoke p_field) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
            let name_str = Swig.get_string ((Swig.invoke name) "as_str" (Swig.C_void)) in
            let name_upper = name_str ^ "_upper" in
            let name_lower = name_str ^ "_lower" in
            let ub_var = LVal(Var(name_upper,Int(4))) in
            let lb_var = LVal(Var(name_lower,Int(4))) in
            [ub_var;lb_var] @ (get_param_vars size (loc + 1) actuals_in p_str)
          with _ ->
            let p_fields = ((Swig.invoke p_ast) "fields" (Swig.C_void)) in
            let addr = ((Swig.invoke p_fields) "[]" (Swig.C_int 1)) in
            let addr_ast = ((Swig.invoke addr) "as_ast" (Swig.C_void)) in
            let a_fields = ((Swig.invoke addr_ast) "fields" (Swig.C_void)) in
            let exprs = ((Swig.invoke a_fields) "[]" (Swig.C_int 0)) in
            let exprs_ast = ((Swig.invoke exprs) "as_ast" (Swig.C_void)) in
            let e_fields = ((Swig.invoke exprs_ast) "fields" (Swig.C_void)) in
            let f0 = ((Swig.invoke e_fields) "[]" (Swig.C_int 0)) in
            let lb = parse_var f0 in
            let f1 = ((Swig.invoke e_fields) "[]" (Swig.C_int 1)) in
            let ub = parse_var f1 in
            [ub;lb] @ (get_param_vars size (loc + 1) actuals_in p_str)
        end
        else begin
          let p_var = parse_var p_field in
          p_var :: (get_param_vars size (loc + 1) actuals_in p_str)
        end
      end
      else begin
        let p_var = parse_var p_field in
        p_var :: (get_param_vars size (loc + 1) actuals_in p_str)
      end
    end
    else begin
      let p_var = parse_var p_field in
      p_var :: (get_param_vars size (loc + 1) actuals_in p_str)
    end
  end

  (*Iterates through the points following a call in order to get the variable id of the return - Needed because
  the return assignment isn't given until a variable number of points past the call point*)
  let rec iter_points size point =
  if (size == 0) then point
  else
  let curPoint = ((Swig.invoke point) "solitary_cfg_target" (Swig.C_void)) in
  let point_string = Swig.get_string ((Swig.invoke curPoint) "as_string" (Swig.C_void)) in
  (*Printf.printf "iterpoint: %s\n" point_string;*)
  iter_points (size-1) curPoint;;

  (* Given a binary op, convert it to + or - (or the opposite if necessary) *)
  let convert_op op_str =
    if (String.compare op_str "+") = 0 then begin Add end
    else if (String.compare op_str "-") = 0 then begin Sub end
    else if (String.compare op_str "*") = 0 then begin Mult end
    else if (String.compare op_str "/") = 0 then begin Div end
    else if (String.compare op_str "%") = 0 then begin Rem end
    else begin Rem end

  let convert_bop op_str =
    if (String.compare op_str "&" = 0) then begin BAnd end
    else if (String.compare op_str "^") = 0 then begin BXor end
    else if (String.compare op_str "b") = 0 then begin BOr end
    else if (String.compare op_str "<") = 0 then begin LShift end
    else if (String.compare op_str ">") = 0 then begin RShift end
    else begin RShift end


  (*Returns the inst representing an instruction - If the point doesn't represent an inst, return _*)
  let point_to_inst point =
  try
    let point_string = Swig.get_string ((Swig.invoke point) "as_string" (Swig.C_void)) in
    (*Printf.printf "Point: %s\n" point_string;*)
    let node_kind = ((Swig.invoke point) "get_kind" (Swig.C_void)) in
    let node_kind_str = (Swig.get_string ((Swig.invoke node_kind) "as_string" (Swig.C_void))) in
    if (((String.compare node_kind_str "label") = 0) || ((String.compare node_kind_str "entry") = 0) || ((String.compare node_kind_str "return") = 0) || ((String.compare node_kind_str "exit") = 0) || ((String.compare node_kind_str "control-point") = 0) || ((String.compare node_kind_str "actual-in") = 0) || ((String.compare node_kind_str "actual-out") = 0) || ((String.compare node_kind_str "jump") = 0)) (*//FIXME: turn control-point off with flag later*) then begin
      []
    end
    (* This is a function call *)
    else if (String.compare node_kind_str "call-site") = 0 then begin
      prev_call := false;
      let func_name = (Swig.get_string ((Swig.invoke point) "as_string" (Swig.C_void))) in
      (*ICall of id option * id * var list *)
      if (String.compare func_name "[call-site] Ljava/lang/Thread::sleep:void(long)") = 0 then begin
        let actuals_in = ((Swig.invoke point) "actuals_in_as_list" (Swig.C_void)) in
        let act_in_size = Swig.get_int ((Swig.invoke actuals_in) "size" (Swig.C_void)) in
        let var_list = get_param_vars act_in_size 0 actuals_in "" in
        let var_slp = List.hd var_list in
        match var_slp with
          LVal(Constant(a,b)) -> let slp_val = a*1000000 in
                                 [Tick(LVal(Var("bytecodecost",Int(4))),LVal(Constant(slp_val,4)))]
          | _ ->  [Tick(LVal(Var("bytecodecost",Int(4))),LVal(Constant(1,4)))]
      end
      else begin
      (* This is regular function call *)
      let call_ast = ((Swig.invoke point) "get_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
      let fields = ((Swig.invoke call_ast) "fields" (Swig.C_void)) in
      let call_name = ((Swig.invoke fields) "[]" (Swig.C_int 0)) in
      let call_name_ast = ((Swig.invoke call_name) "as_ast" (Swig.C_void)) in
      let call_name_ast_str = Swig.get_string ((Swig.invoke call_name_ast) "as_string" (Swig.C_void)) in
      let fn_name = (String.sub func_name 12 ((String.length func_name)-12)) in
      let actuals_in = ((Swig.invoke point) "actuals_in_as_list" (Swig.C_void)) in
      let act_in_size = Swig.get_int ((Swig.invoke actuals_in) "size" (Swig.C_void)) in
      (*Get the string representation of the arguments*)
      let var_list = (if (act_in_size > 0) then begin
        get_param_vars act_in_size 0 actuals_in ""
      end
      else [])
      in
      let cur_funct = List.find (fun x -> x.fname = fn_name) !procs_lst in
      let arg_list = cur_funct.fargs in
      let same_length = (List.length arg_list = List.length var_list) in
      let actuals_out = ((Swig.invoke point) "actuals_out_as_list" (Swig.C_void)) in
      let act_out_size = Swig.get_int ((Swig.invoke actuals_out) "size" (Swig.C_void)) in
      (*Iterate through the following points until the return point is reached*)
      let c_point = iter_points act_in_size point in
      if (act_out_size > 0) then begin
        prev_call := true;
        let cur_point = iter_points (act_out_size+1) c_point in
        let return_ast = ((Swig.invoke cur_point) "get_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
        let assign_fields = ((Swig.invoke return_ast) "fields" (Swig.C_void)) in
        let assign_field = (Swig.invoke assign_fields) "[]" (Swig.C_int 0) in
        let assign_ast = (Swig.invoke assign_field) "as_ast" (Swig.C_void) in
        let sym_type = ((Swig.invoke assign_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
        let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
        let ty = get_type sym_type_str in
        let assign = Swig.get_string ((Swig.invoke ((Swig.invoke assign_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void)))) "as_str" (Swig.C_void)) in
        (if not (List.mem (Var(assign,ty)) !cur_args) then begin
          (if not (List.mem (Var(assign,ty)) !glos) then begin
            (if not (List.mem (Var(assign,ty)) !cur_locs) then begin
               cur_locs := Var(assign,ty) :: !cur_locs end)
          end)
        end);
        if same_length then begin
          [Call(Some(LVal(Var(assign,ty))),fn_name,var_list)]
        end else begin
          [Call(Some(LVal(Var(assign,ty))),fn_name,[])]
        end
      end else begin
        if same_length then begin
          [Call(None,fn_name,var_list)]
        end else begin
          [Call(None,fn_name,[])]
        end
      end
    end
    end
    (* This is a normal expression, create an appropriate C4B instruction, either set or increment *)
    else if (String.compare node_kind_str "expression") = 0 then begin (*C4B-INC, C4B-SET*)
      if !prev_call then begin prev_call := false; [] end else begin
        try
          (* Grab the field information from the AST *)
          let exp_ast = ((Swig.invoke point) "get_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
          let ast_class = ((Swig.invoke exp_ast) "get_class" (Swig.C_void)) in
          let ast_string = (Swig.get_string ((Swig.invoke ast_class) "as_string" (Swig.C_void))) in
          (*Printf.printf "ASTExpressionClass: %s\n" ast_string;*)
          if (String.compare ast_string "c:assume-expr") = 0 then begin
            let fields = ((Swig.invoke exp_ast) "fields" (Swig.C_void)) in
            let f1 = ((Swig.invoke fields) "[]" (Swig.C_int 0)) in  let pred = ((Swig.invoke point) "cfg_predecessors" (Swig.C_void)) in
            let cond_ast = ((Swig.invoke f1) "as_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
            let cond_class = ((Swig.invoke cond_ast) "get_class" (Swig.C_void)) in
            let cond_class_str = (Swig.get_string ((Swig.invoke cond_class) "as_string" (Swig.C_void))) in
            (*Get the string reresentation of the comparison operator - this can be 1 or 2 characters long*)
            let conditional = (try String.sub cond_class_str 2 2 with
              Invalid_argument _ -> (String.sub cond_class_str 2 1)) in
            let cond = get_conditional conditional false in
            let fields2 = ((Swig.invoke cond_ast) "fields" (Swig.C_void)) in
            (* cond is lsum*comp*lsum*)
            let lh = ((Swig.invoke fields2) "[]" (Swig.C_int 0)) in
            let rh = ((Swig.invoke fields2) "[]" (Swig.C_int 1)) in
            let lh_ast = ((Swig.invoke lh) "as_ast" (Swig.C_void)) in
            let rh_ast = ((Swig.invoke rh) "as_ast" (Swig.C_void)) in
            let lh_class = ((Swig.invoke lh_ast) "get_class" (Swig.C_void)) in
            let lh_class_str = Swig.get_string ((Swig.invoke lh_class) "as_string" (Swig.C_void)) in
            let left_hand = (if (String.compare lh_class_str "c:dot") = 0 then
              Some(parse_dot lh_ast) else
              parse_lsum lh) in
            let rh_class = ((Swig.invoke rh_ast) "get_class" (Swig.C_void)) in
            let rh_class_str = Swig.get_string ((Swig.invoke rh_class) "as_string" (Swig.C_void)) in
            let right_hand = (if (String.compare rh_class_str "c:dot") = 0 then
              Some(parse_dot rh_ast) else
              parse_lsum rh) in
            match left_hand with
              None -> []
            | Some (lft) -> (
              match right_hand with
                None -> []
              | Some(rgt) ->
              [Assume(Cond(lft,cond,rgt))]
            );
          end
          else begin
          let fields = ((Swig.invoke exp_ast) "fields" (Swig.C_void)) in
          let f1 = ((Swig.invoke fields) "[]" (Swig.C_int 0)) in
          let f1_ast = ((Swig.invoke f1) "as_ast" (Swig.C_void)) in
          let f1_class = ((Swig.invoke f1_ast) "get_class" (Swig.C_void)) in
          let f1_class_str = Swig.get_string ((Swig.invoke f1_class) "as_string" (Swig.C_void)) in
          (*Printf.printf "f1_class: %s\n" f1_class_str;*)
          let array_store = ref false in
          let lh = (if ((String.compare "c:dot" f1_class_str) = 0) then begin
              let f1_fields = ((Swig.invoke f1_ast) "fields" (Swig.C_void)) in
              let f1_f1 = ((Swig.invoke f1_fields) "[]" (Swig.C_int 0)) in
              let f1_f1_ast = ((Swig.invoke f1_f1) "as_ast" (Swig.C_void)) in
              let f1_f1_field = ((Swig.invoke f1_f1_ast) "fields" (Swig.C_void)) in
              let f1_f1_f0 = ((Swig.invoke f1_f1_field) "[]" (Swig.C_int 0)) in
              let f1_f1_f0_ast = ((Swig.invoke f1_f1_f0) "as_ast" (Swig.C_void)) in
              let f1_f1_f0_class = ((Swig.invoke f1_f1_f0_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
              let f1_f1_f0_class_str = Swig.get_string ((Swig.invoke f1_f1_f0_class) "as_string" (Swig.C_void)) in
              array_store := true;
              if (String.length f1_f1_f0_class_str > 35) then begin
                let sub_str = (String.sub f1_f1_f0_class_str 24 12) in
                (*Printf.printf "sub_str: %s\n" sub_str;*)
                if (String.compare sub_str "abs_interval") = 0 then begin
                  (*Printf.printf "Yay!\n";*)
                  parse_dot f1_ast
                end
                else begin
                  parse_length f1_f1
                end
              end
              else begin
                parse_length f1_f1
              end
            end
            else if ((String.compare "c:ptr" f1_class_str) = 0) then begin
              array_store := true;
              parse_array_access f1 end
            else begin
              let f1_name = ((Swig.invoke f1_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
              let f1_name_str = Swig.get_string ((Swig.invoke f1_name) "as_str" (Swig.C_void)) in
              let sym_type = ((Swig.invoke f1_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
              let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
              let ty = get_type sym_type_str in
              (* Add the left hand value to the local list if needed *)
              (if not (List.mem (Var(f1_name_str,ty)) !cur_args) then begin
                (if not (List.mem (Var(f1_name_str,ty)) !glos) then begin
                  (if not (List.mem (Var(f1_name_str,ty)) !cur_locs) then begin
                    cur_locs := Var(f1_name_str,ty) :: !cur_locs end)
                end)
              end);
              LVal(Var(f1_name_str,ty)) end) in
          let f2 = ((Swig.invoke fields) "[]" (Swig.C_int 1)) in
          let f2_ast = ((Swig.invoke f2) "as_ast" (Swig.C_void)) in
          let f2_str = Swig.get_string ((Swig.invoke f2_ast) "as_string" (Swig.C_void)) in
          let f2_class = ((Swig.invoke f2_ast) "get_class" (Swig.C_void)) in
          let f2_class_str = Swig.get_string ((Swig.invoke f2_class) "as_string" (Swig.C_void)) in
          let f2_class_super = ((Swig.invoke f2_class) "superclass" (Swig.C_void)) in
          let f2_class_super_str = Swig.get_string ((Swig.invoke f2_class_super) "as_string" (Swig.C_void)) in
          if (String.compare f2_class_super_str "c:arithmetic") = 0 then begin
            let f2_fields = ((Swig.invoke f2_ast) "fields" (Swig.C_void)) in
            let f2_f1 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 0)) in
            let f2_f1_ast = ((Swig.invoke f2_f1) "as_ast" (Swig.C_void)) in
            (* check for negative nums, they lack some of the fields below *)
            if !array_store then begin
              let f2_f2 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 1)) in
              let f_var = parse_var f2_f2 in
              let f_var2 = parse_var f2_f1 in
              let f1_possible_op = (String.sub f2_class_str 2 1) in
              let op = convert_op f1_possible_op in
              [BinExpr(lh,f_var2,op,f_var)]
            end
            else begin
              let f2_f1_name_str = Swig.get_string ((Swig.invoke ((Swig.invoke f2_f1_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void)))) "as_str" (Swig.C_void)) in
              let f1_name = ((Swig.invoke f1_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
              let f1_name_str = Swig.get_string ((Swig.invoke f1_name) "as_str" (Swig.C_void)) in
              if ((String.compare f2_f1_name_str f1_name_str) = 0) then begin
                let f2_f2 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 1)) in
                let f_var = parse_var f2_f2 in
                let f_var2 = parse_var f2_f1 in
                let op = convert_op (String.sub f2_class_str 2 1) in
                [BinExpr(lh,f_var2,op,f_var)]
              end
              else begin
                let f2_f2 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 1)) in
                let f_var = parse_var f2_f2 in
                let f_var2 = parse_var f2_f1 in
                let f1_possible_op = (String.sub f2_class_str 2 1) in
                let op = convert_op f1_possible_op in
                [BinExpr(lh,f_var2,op,f_var)]
              end
            end
          end
          else if (String.compare f2_class_super_str "c:logical") = 0 then begin
            let f2_fields = ((Swig.invoke f2_ast) "fields" (Swig.C_void)) in
            let f2_f1 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 0)) in
            let f2_f1_ast = ((Swig.invoke f2_f1) "as_ast" (Swig.C_void)) in
            (* check for negative nums, they lack some of the fields below *)
            if !array_store then begin
              let f2_f2 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 1)) in
              let f_var = parse_var f2_f2 in
              let f_var2 = parse_var f2_f1 in
              let f1_possible_op = (String.sub f2_class_str 2 1) in
              let op = convert_bop f1_possible_op in
              [BinExpr(lh,f_var2,op,f_var)]
            end
            else begin
              let f2_f1_name_str = Swig.get_string ((Swig.invoke ((Swig.invoke f2_f1_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void)))) "as_str" (Swig.C_void)) in
              let f1_name = ((Swig.invoke f1_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
              let f1_name_str = Swig.get_string ((Swig.invoke f1_name) "as_str" (Swig.C_void)) in
              if ((String.compare f2_f1_name_str f1_name_str) = 0) then begin
                let f2_f2 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 1)) in
                let f_var = parse_var f2_f2 in
                let f_var2 = parse_var f2_f1 in
                let op = convert_bop (String.sub f2_class_str 2 1) in
                [BinExpr(lh,f_var2,op,f_var)]
              end
              else begin
                let f2_f2 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 1)) in
                let f_var = parse_var f2_f2 in
                let f_var2 = parse_var f2_f1 in
                let f1_possible_op = (String.sub f2_class_str 2 1) in
                let op = convert_bop f1_possible_op in
                [BinExpr(lh,f_var2,op,f_var)]
              end
            end
          end
          (*else if  Dot class (this means struct access) *)
          else begin
            (*Printf.printf "SuperClass: %s\n" f2_class_super_str;*)
            if ((String.compare "c:dot" f2_class_str) = 0) then begin
              let f2_fields = ((Swig.invoke f2_ast) "fields" (Swig.C_void)) in
              let f2_f1 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 0)) in
              let f2_f1_ast = ((Swig.invoke f2_f1) "as_ast" (Swig.C_void)) in
              let f2_f1_field = ((Swig.invoke f2_f1_ast) "fields" (Swig.C_void)) in
              let f2_f1_f0 = ((Swig.invoke f2_f1_field) "[]" (Swig.C_int 0)) in
              let f2_f1_f0_ast = ((Swig.invoke f2_f1_f0) "as_ast" (Swig.C_void)) in
              let f2_f1_f0_class = ((Swig.invoke f2_f1_f0_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
              let f2_f1_f0_class_str = Swig.get_string ((Swig.invoke f2_f1_f0_class) "as_string" (Swig.C_void)) in
              (*Printf.printf "dot_string: %s\n" f2_f1_f0_class_str;*)
              array_store := true;
              let rh = (if (String.length f2_f1_f0_class_str > 35) then begin
                let sub_str = (String.sub f2_f1_f0_class_str 24 12) in
                if (String.compare sub_str "abs_interval") = 0 then begin
                  parse_dot f2_ast
                end
                else begin
                  parse_length f2_f1
                end
              end
              else begin
                parse_length f2_f1
              end) in
              [Assign(lh,rh)]
            end
            else if ((String.compare "c:ptr" f2_class_str) = 0) then begin
              let f2_fields = ((Swig.invoke f2_ast) "fields" (Swig.C_void)) in
              let rh = parse_array_access f2 in
              [Assign(lh,rh)]
            end
            else begin
              if (String.compare f2_class_str "c:exprs") = 0 then begin
                let name = (match lh with LVal(Var(rh_name,_)) ->
                rh_name
                | _ -> "") in
                let name_u = name ^ "_upper" in
                let name_l = name ^ "_lower" in
                let l_var = LVal(Var(name_l,Int(4))) in
                let u_var = LVal(Var(name_u,Int(4))) in
                let f2_fields = ((Swig.invoke f2_ast) "fields" (Swig.C_void)) in
                let f2_f1 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 0)) in
                let f2_f1_ast = ((Swig.invoke f2_f1) "as_ast" (Swig.C_void)) in
                let f2_f1_string = Swig.get_string ((Swig.invoke f2_f1_ast) "as_string" (Swig.C_void)) in
                let f2_f2 = ((Swig.invoke f2_fields) "[]" (Swig.C_int 1)) in
                let f2_f2_ast = ((Swig.invoke f2_f2) "as_ast" (Swig.C_void)) in
                try
                let f2_f1_class = ((Swig.invoke f2_f1_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
                let f2_f1_class_str = Swig.get_string ((Swig.invoke f2_f1_class) "as_string" (Swig.C_void)) in
                let rh_l = parse_var f2_f1 in
                let rh_u = parse_var f2_f2 in
                [Assign(l_var,rh_l);Assign(u_var,rh_u)]
                with _ -> (
                  let rh_l = parse_dot f2_f1_ast in
                  let rh_u = parse_dot f2_f2_ast in
                  [Assign(l_var,rh_l);Assign(u_var,rh_u)]
                )
              end
              else begin
              let f_var = parse_var f2 in
              let f1_name = ((Swig.invoke f1_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
              let f1_name_str = Swig.get_string ((Swig.invoke f1_name) "as_str" (Swig.C_void)) in
              let bc = String.compare f1_name_str "bytecodecost" in
              if bc = 0 then begin
                [Tick(lh,f_var)]
              end
              else begin
                [Assign(lh,f_var)]
              end
              end
            end
          end
        end
        with
          | _ -> []
      end
    end
    else begin
      prev_call := false;
      []
    end
  with
    | _ -> []

  (* For a list of points, iterate and convert the current point *)
  let rec convert_instructions current last inst_list prev_list =
  let point_string = Swig.get_string ((Swig.invoke current) "as_string" (Swig.C_void)) in
  (*Printf.printf "point: %s\n" point_string;*)
  let last_string = Swig.get_string ((Swig.invoke last) "as_string" (Swig.C_void)) in
  (*Printf.printf "last: %s\n" last_string;*)
  let next_list = point_to_inst current in
  let next_point = (
    if !was_assert then begin
      iter_points 1 current end
    else begin
      current end
  ) in
  let updated_list = (
    if !was_assert then begin
      inst_list end
    else begin
      inst_list @ prev_list end
  ) in
  was_assert := false;
  let equality = Swig.get_bool ((Swig.invoke next_point) "==" (last)) in
  if equality then begin
    inst_list @ prev_list @ next_list
  end else begin
    let convert_point = ((Swig.invoke next_point) "solitary_cfg_target" (Swig.C_void)) in
    convert_instructions convert_point last updated_list next_list
  end;;

  (* For each block, convert the points of instructions *)
  let convert_block_insts block =
  let f_point = ((Swig.invoke block) "first_point" (Swig.C_void)) in
  let l_point = ((Swig.invoke block) "last_point" (Swig.C_void)) in
    convert_instructions f_point l_point [] [];;

  (* Given a control point (a conditional instruction) create a precondition of the appropriate child blocks *)
  let create_cond point =
  let node_kind = ((Swig.invoke point) "get_kind" (Swig.C_void)) in
  let node_kind_str = (Swig.get_string ((Swig.invoke node_kind) "as_string" (Swig.C_void))) in
  if ((String.compare node_kind_str "control-point") = 0) then begin
    let cond_ast = ((Swig.invoke point) "get_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
    let cond_class = ((Swig.invoke cond_ast) "get_class" (Swig.C_void)) in
    let cond_class_str = (Swig.get_string ((Swig.invoke cond_class) "as_string" (Swig.C_void))) in
    (*Get the string reresentation of the comparison operator - this can be 1 or 2 characters long*)
    let conditional = (try String.sub cond_class_str 2 2 with
      Invalid_argument _ -> (String.sub cond_class_str 2 1)) in
    let cond = get_conditional conditional false in
    let fields2 = ((Swig.invoke cond_ast) "fields" (Swig.C_void)) in
    let left_hand = parse_lsum ((Swig.invoke fields2) "[]" (Swig.C_int 0)) in
    let right_hand = parse_lsum ((Swig.invoke fields2) "[]" (Swig.C_int 1)) in
    match left_hand with
      None -> Some(NonDet)
    | Some(lft) -> (
        match right_hand with
          None -> Some(NonDet)
        | Some(rgt) -> Some(Cond(lft,cond,rgt))
    )
  end
  else
      Some(Jmp)

  (* Takes the current functions return variable, a basic block, the list of  all ready visited basic blocks, and a precondition
  and returns the list of basic block representations for all the later blocks, the list of all ready visited block ids, the current id, and the list of
  block predecessors for this block *)
  let rec get_blocks_helper basic_block return_var already_checked : (bblock list * (int * int) list * int * (int * int) list) =
  let inst_list = convert_block_insts basic_block in
  let first_point = ((Swig.invoke basic_block) "first_point" (Swig.C_void)) in
  let point_string = Swig.get_string ((Swig.invoke first_point) "as_string" (Swig.C_void)) in
  let last_point = ((Swig.invoke basic_block) "last_point" (Swig.C_void)) in
  let cfg_targets = ((Swig.invoke last_point) "cfg_targets" (Swig.C_void)) in
  let cfg_targets_v = ((Swig.invoke cfg_targets) "to_vector" (Swig.C_void)) in
  let size = (Swig.get_int ((Swig.invoke cfg_targets_v) "size" (Swig.C_void))) in
  let cur_id = !node_id in
  node_id := !node_id + 1;
  (*Printf.printf "BB\n";*)
  if size > 0 then begin
    let collected_blocks = ref [] in
    let children_block_ids = ref [] in
    let total_ac = ref [] in
    let ac = ref [] in
    ac := already_checked;
    let bp_list = ref [] in
    (* For each child block *)
    for j = (size - 1) downto 0 do
      let edge = ((Swig.invoke cfg_targets_v) "[]" (Swig.C_int j)) in (*cfg_edge is (point,edge) std::pair*)
      let point = ((Swig.invoke edge) "get_first" (Swig.C_void)) in  (*extract from tuple*)
      let point_id = (Swig.get_int ((Swig.invoke point) "id" (Swig.C_void))) in
      let is_point = List.mem_assoc point_id !blk_preds in
      (* If this this block isn't in the list of block preds for the child block, add it *)
      (if not (is_point) then begin
      blk_preds := ((point_id, [cur_id]) :: !blk_preds);
      end
      else begin
        let cur_preds = List.assoc point_id !blk_preds in
        let updated_preds = List.remove_assoc point_id !blk_preds in
        blk_preds := ((point_id, cur_id :: cur_preds) :: updated_preds)
      end);
      (* Check to be sure that we haven't all ready visited the child block *)
      if not (List.mem_assoc point_id !ac) then begin   (* have to account for infinite loops *)
        ac := (point_id, -1) :: !ac;
        let next_block = ((Swig.invoke point) "get_basic_block" (Swig.C_void)) in
        (* NOTE: if there's more than 2 branch points, the first gets the "then" conditional
            as an assert, the REST get the "else" conditional *)
        (* call get_blocks_helper on the child block *)
        let ret = get_blocks_helper next_block return_var !ac in
          match ret with
          (* update the various lists before preceeding with the loop *)
          (blocks, point_block_map, first_bId, bId_point_list) ->
            let new_ac : (int * int) list = point_block_map in
            let new_bp : (int * int) list = bId_point_list in
              children_block_ids := first_bId :: !children_block_ids;
              collected_blocks := !collected_blocks @ blocks;
              total_ac := !total_ac @ new_ac;
              ac := !ac @ new_ac;
              bp_list := !bp_list @ new_bp
      end
      else begin
        children_block_ids := (0-point_id) :: !children_block_ids
      end
    done ;
    let new_cond = create_cond last_point in
    (* The child blocks have been dealt with, create the blkdesc for the current block *)
    let blk = {bpreds=[];binsts=inst_list;btype=Branch(!children_block_ids);bcond=new_cond} in
    let f_point_id = (Swig.get_int ((Swig.invoke first_point) "id" (Swig.C_void))) in
    total_ac := (f_point_id, cur_id) :: !total_ac;
    bp_list := (cur_id, f_point_id) :: !bp_list;
    (blk :: !collected_blocks),!total_ac,cur_id,!bp_list
  end
  else begin
  (* This block has no children, so it's a return block *)
    let ret_block = {bpreds=[];binsts=inst_list;btype=Return(return_var);bcond=None} in
    let f_point_id = (Swig.get_int ((Swig.invoke first_point) "id" (Swig.C_void))) in
    let cur_ac = [(f_point_id,cur_id)] in
    let cur_bp = [(cur_id,f_point_id)] in
    [ret_block],cur_ac,cur_id,cur_bp
  end

  (* ***********wrapper for getting blocks, post processing back edges *)
  let get_blocks point_node return_var already_checked: bblock list =
    let null_prec = None in
    node_id := 0;
    blk_preds := [];
    let entry_block = ((Swig.invoke point_node) "get_basic_block" (Swig.C_void)) in
    let blocks, point_to_block_id_map, _, block_to_point_map = (get_blocks_helper entry_block return_var already_checked) in
    let cur_id = ref 0 in
    let post_process_block block =
      (match block with
      {btype=btyp} ->
        let fix_ids x : int =
          if x < 0 then
            let id = 0 - x in
            if (List.mem_assoc (id) point_to_block_id_map)
            then (List.assoc id point_to_block_id_map)
            else (begin
              Printf.printf "***BACK EDGE FOR NODE [%d] NOT FOUND IN MAP -- ERROR.\n" id ;
              -1
             end)
           else
             x
        in
        let new_branch = (match btyp with
          | Branch (child_ids) ->
            let new_child_ids : int list = List.map fix_ids child_ids in
            Branch(new_child_ids)
          | _ -> btyp
        ) in
        let p_id = (if not (List.mem_assoc (!cur_id) block_to_point_map) then begin
          Printf.printf "ERROR: MISSING BB ID\n";
            1 end
        else List.assoc !cur_id block_to_point_map) in
        let preds =
          (if not (List.mem_assoc p_id !blk_preds) then begin [-1] end
          else begin List.assoc p_id !blk_preds end) in
        cur_id := !cur_id + 1;
        let up_block = {block with btype = new_branch} in
          {up_block with bpreds = preds})
    in
      List.map post_process_block blocks

  (* **********function to print locals for a procedure *)
  let get_locals proc args = (*C4B-FLOCS*)
  let ret = ref [] in
  (try
    let locals = ((Swig.invoke proc) "local_symbols" (Swig.C_void)) in
    while not (Swig.get_bool ((Swig.invoke locals) "at_end" (Swig.C_void))) do
      let symbol = ((Swig.invoke locals) "__ref__" (Swig.C_void)) in
        ((Swig.invoke locals) "advance" (Swig.C_void));
      let param_ast = ((Swig.invoke symbol) "get_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
      if (Swig.get_bool ((Swig.invoke param_ast) "has_field" (Cs._ast_ordinal_NC_NAME(Swig.C_void)))) then
        let name = ((Swig.invoke param_ast) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
        let name_str = (Swig.get_string ((Swig.invoke name) "as_str" (Swig.C_void))) in
        (try
          let idx = String.index name_str '$' in
          let res_sub = String.sub name_str (idx + 1) 6 in
          if res_sub <> "result" then begin
            let sym_type = ((Swig.invoke symbol) "get_type" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
            let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
            if (String.length sym_type_str > 16) then begin
              let sub_type = String.sub sym_type_str 7 10 in
              if ((String.compare sub_type "java_array") = 0) then begin
                let name_length = name_str ^ "_length" in
                let name_array = name_str ^ "_array" in
                let p_fields = ((Swig.invoke param_ast) "fields" (Swig.C_void)) in
                let typ = ((Swig.invoke p_fields) "[]" (Swig.C_int 1)) in
                let typ_ast = ((Swig.invoke typ) "as_ast" (Swig.C_void)) in
                let typ_fields = ((Swig.invoke typ_ast) "fields" (Swig.C_void)) in
                let ty_f = ((Swig.invoke typ_fields) "[]" (Swig.C_int 1)) in
                let array_t = ((Swig.invoke ty_f) "as_ast" (Swig.C_void)) in
                let array_t_fields = ((Swig.invoke array_t) "fields" (Swig.C_void)) in
                let array_type = ((Swig.invoke array_t_fields) "[]" (Swig.C_int 1)) in
                let ptr_t = ((Swig.invoke array_type) "as_ast" (Swig.C_void)) in
                let ptr_type = ((Swig.invoke ptr_t) "[]" (Cs._ast_ordinal_NC_POINTED_TO(Swig.C_void))) in
                let ptd_to = ((Swig.invoke ptr_type) "as_ast" (Swig.C_void)) in
                let type_string = Swig.get_string ((Swig.invoke ptd_to) "as_string" (Swig.C_void)) in
                let ty = get_type type_string in
                if not (List.mem (Var(name_length,Int(4))) args) then begin
                  ret := Var(name_length,Int(4)) :: !ret;
                  ret := Var(name_array,Array(ty)) :: !ret;
                end
              end
              else if (String.length sym_type_str > 18) then begin
                let sub_type_a = String.sub sym_type_str 7 12 in
                if ((String.compare sub_type_a "abs_interval") = 0) then begin
                  let name_upper = name_str ^ "_upper" in
                  let name_lower = name_str ^ "_lower" in
                  if not (List.mem (Var(name_upper,Int(4))) args) then begin
                    ret := Var(name_upper,Int(4)) :: !ret;
                    ret := Var(name_lower,Int(4)) :: !ret;
                  end
                end
                else begin
                  let ty = get_type sym_type_str in
                  if not (List.mem (Var(name_str,ty)) args) then begin
                    ret := (List.append !ret [Var(name_str,ty)]);
                  end
                end
              end
              else begin
                let ty = get_type sym_type_str in
                if not (List.mem (Var(name_str,ty)) args) then begin
                  ret := Var(name_str,ty)::!ret end
              end
            end
            else begin
              let ty = get_type sym_type_str in
              if not (List.mem (Var(name_str,ty)) args) then begin
                ret := Var(name_str,ty)::!ret end
            end
          end;
        with
          | _ -> (
          let sym_type = ((Swig.invoke symbol) "get_type" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
            let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
            if (String.length sym_type_str > 16) then begin
              let sub_type = String.sub sym_type_str 7 10 in
              if ((String.compare sub_type "java_array") = 0) then begin
                let name_length = name_str ^ "_length" in
                let name_array = name_str ^ "_array" in
                let p_fields = ((Swig.invoke param_ast) "fields" (Swig.C_void)) in
                let typ = ((Swig.invoke p_fields) "[]" (Swig.C_int 1)) in
                let typ_ast = ((Swig.invoke typ) "as_ast" (Swig.C_void)) in
                let typ_fields = ((Swig.invoke typ_ast) "fields" (Swig.C_void)) in
                let ty_f = ((Swig.invoke typ_fields) "[]" (Swig.C_int 1)) in
                let array_t = ((Swig.invoke ty_f) "as_ast" (Swig.C_void)) in
                let array_t_fields = ((Swig.invoke array_t) "fields" (Swig.C_void)) in
                let array_type = ((Swig.invoke array_t_fields) "[]" (Swig.C_int 1)) in
                let ptr_t = ((Swig.invoke array_type) "as_ast" (Swig.C_void)) in
                let ptr_type = ((Swig.invoke ptr_t) "[]" (Cs._ast_ordinal_NC_POINTED_TO(Swig.C_void))) in
                let ptd_to = ((Swig.invoke ptr_type) "as_ast" (Swig.C_void)) in
                let type_string = Swig.get_string ((Swig.invoke ptd_to) "as_string" (Swig.C_void)) in
                let ty = get_type type_string in
                if not (List.mem (Var(name_length,Int(4))) args) then begin
                  ret := Var(name_length,Int(4)) :: !ret;
                  ret := Var(name_array,Array(ty)) :: !ret;
                end
              end
              else if (String.length sym_type_str > 18) then begin
                let sub_type_a = String.sub sym_type_str 7 12 in
                if ((String.compare sub_type_a "abs_interval") = 0) then begin
                  let name_upper = name_str ^ "_upper" in
                  let name_lower = name_str ^ "_lower" in
                  if not (List.mem (Var(name_upper,Int(4))) args) then begin
                    ret := Var(name_upper,Int(4)) :: !ret;
                    ret := Var(name_lower,Int(4)) :: !ret;
                  end
                end
                else begin
                  let ty = get_type sym_type_str in
                  if not (List.mem (Var(name_str,ty)) args) then begin
                    ret := (List.append !ret [Var(name_str,ty)]);
                  end
                end
              end
              else begin
                let ty = get_type sym_type_str in
                if not (List.mem (Var(name_str,ty)) args) then begin
                  ret := Var(name_str,ty)::!ret end
              end
            end
            else begin
              let ty = get_type sym_type_str in
              if not (List.mem (Var(name_str,ty)) args) then begin
                ret := Var(name_str,ty)::!ret end
            end));
    done
  with
  | _ -> ());
  !ret

  (* **********function to print parameters for a procedure *)
  let get_funargs proc = (*C4B-FARGS*)
  let ret = ref [] in
    (try
      let args = ((Swig.invoke proc) "formal_ins_vector" (Swig.C_void)) in
      let size = (Swig.get_int ((Swig.invoke args) "size" (Swig.C_void))) in
      for j = 0 to (size - 1) do
        let arg = ((Swig.invoke args) "[]" (Swig.C_int j)) in
        let arg_ast = ((Swig.invoke arg) "get_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
        let fields = ((Swig.invoke arg_ast) "fields" (Swig.C_void)) in
        if ((Swig.get_int ((Swig.invoke fields) "size" (Swig.C_void))) > 0) then
          let param = ((Swig.invoke fields) "[]" (Swig.C_int 0)) in
          if (Swig.get_bool ((Swig.invoke param) "has_field" (Cs._ast_ordinal_NC_NAME(Swig.C_void)))) then
            let name = ((Swig.invoke param) "[]" (Cs._ast_ordinal_NC_NAME(Swig.C_void))) in
            let name_str = Swig.get_string ((Swig.invoke name) "as_str" (Swig.C_void)) in
            let param_ast = ((Swig.invoke param) "as_ast" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
            let sym_type = ((Swig.invoke param_ast) "[]" (Cs._ast_ordinal_NC_TYPE(Swig.C_void))) in
            let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
            if (String.length sym_type_str > 33) then begin
              let sub_type = String.sub sym_type_str 24 10 in
              if ((String.compare sub_type "java_array") = 0) then begin
                let name_length = name_str ^ "_length" in
                let name_array = name_str ^ "_array" in
                let p_fields = ((Swig.invoke param_ast) "fields" (Swig.C_void)) in
                let typ = ((Swig.invoke p_fields) "[]" (Swig.C_int 1)) in
                let typ_ast = ((Swig.invoke typ) "as_ast" (Swig.C_void)) in
                let typ_fields = ((Swig.invoke typ_ast) "fields" (Swig.C_void)) in
                let ty_f = ((Swig.invoke typ_fields) "[]" (Swig.C_int 1)) in
                let array_t = ((Swig.invoke ty_f) "as_ast" (Swig.C_void)) in
                let array_t_fields = ((Swig.invoke array_t) "fields" (Swig.C_void)) in
                let array_type = ((Swig.invoke array_t_fields) "[]" (Swig.C_int 1)) in
                let ptr_t = ((Swig.invoke array_type) "as_ast" (Swig.C_void)) in
                let ptr_type = ((Swig.invoke ptr_t) "[]" (Cs._ast_ordinal_NC_POINTED_TO(Swig.C_void))) in
                let ptd_to = ((Swig.invoke ptr_type) "as_ast" (Swig.C_void)) in
                let type_string = Swig.get_string ((Swig.invoke ptd_to) "as_string" (Swig.C_void)) in
                let ty = get_type type_string in
                ret := (List.append !ret [Var(name_length,Int(4))]);
                ret := (List.append !ret [Var(name_array,Array(ty))]);
              end
              else if (String.length sym_type_str > 35) then begin
                let sub_type_a = String.sub sym_type_str 24 12 in
                if ((String.compare sub_type_a "abs_interval") = 0) then begin
                  let name_upper = name_str ^ "_upper" in
                  let name_lower = name_str ^ "_lower" in
                  ret := (List.append !ret [Var(name_upper,Int(4))]);
                  ret := (List.append !ret [Var(name_lower,Int(4))]);
                end
                else begin
                  let ty = get_type sym_type_str in
                  ret := (List.append !ret [Var(name_str,ty)]);
                end
              end
              else begin
                let ty = get_type sym_type_str in
                ret := (List.append !ret [Var(name_str,ty)]);
              end;
            end
            else begin
              let ty = get_type sym_type_str in
              ret := (List.append !ret [Var(name_str,ty)]);
            end;
      done
    with
    | _ -> ());
  !ret


  (* Get the list of globals for the compunit *)
  let update_glos c_unit =
    (try
      let g_it = ((Swig.invoke c_unit) "global_symbols" (Swig.C_void)) in
      while not (Swig.get_bool ((Swig.invoke g_it) "at_end" (Swig.C_void))) do
        let cur_sym = ((Swig.invoke g_it) "__ref__" (Swig.C_void)) in
        ((Swig.invoke g_it) "advance" (Swig.C_void));
        if not (Swig.get_bool ((Swig.invoke cur_sym) "is_function" (Swig.C_void))) then begin
          let sym_type = ((Swig.invoke cur_sym) "get_type" (Cs._ast_family_C_NORMALIZED(Swig.C_void))) in
          let sym_type_str = Swig.get_string ((Swig.invoke sym_type) "as_string" (Swig.C_void)) in
          let g_name = (Swig.get_string ((Swig.invoke cur_sym) "name" (Swig.C_void))) in
          if (String.length sym_type_str > 16) then begin
            let sub_type = String.sub sym_type_str 7 10 in
            if ((String.compare sub_type "java_array") = 0) then begin
              let g_name_length = g_name ^ "_length" in
              let g_name_array = g_name ^ "_array" in
              let g_ast = ((Swig.invoke cur_sym) "get_ast" (Swig.C_void)) in
              let g_fields = ((Swig.invoke g_ast) "fields" (Swig.C_void)) in
              let typ = ((Swig.invoke g_fields) "[]" (Swig.C_int 1)) in
              let typ_ast = ((Swig.invoke typ) "as_ast" (Swig.C_void)) in
              let typ_fields = ((Swig.invoke typ_ast) "fields" (Swig.C_void)) in
              let ty_f = ((Swig.invoke typ_fields) "[]" (Swig.C_int 1)) in
              let array_t = ((Swig.invoke ty_f) "as_ast" (Swig.C_void)) in
              let array_t_fields = ((Swig.invoke array_t) "fields" (Swig.C_void)) in
              let array_type = ((Swig.invoke array_t_fields) "[]" (Swig.C_int 1)) in
              let ptr_t = ((Swig.invoke array_type) "as_ast" (Swig.C_void)) in
              let ptr_type = ((Swig.invoke ptr_t) "[]" (Cs._ast_ordinal_NC_POINTED_TO(Swig.C_void))) in
              let ptd_to = ((Swig.invoke ptr_type) "as_ast" (Swig.C_void)) in
              let type_string = Swig.get_string ((Swig.invoke ptd_to) "as_string" (Swig.C_void)) in
              let ty = get_type type_string in
              glos := Var(g_name_length,Int(4)) :: !glos;
              glos := Var(g_name_array,Array(ty)) :: !glos;
            end
            else if (String.length sym_type_str > 18) then begin
              let sub_type_a = String.sub sym_type_str 7 12 in
              if ((String.compare sub_type_a "abs_interval") = 0) then begin
                let g_name_upper = g_name ^ "_upper" in
                let g_name_lower = g_name ^ "_lower" in
                glos := Var(g_name_upper,Int(4)) :: !glos;
                glos := Var(g_name_lower,Int(4)) :: !glos;
              end
              else begin
                let ty = get_type sym_type_str in
                glos := Var(g_name,ty) :: !glos
              end
            end
            else begin
              let ty = get_type sym_type_str in
              glos := Var(g_name,ty) :: !glos
            end;
          end
          else begin
            let ty = get_type sym_type_str in
            glos := Var(g_name,ty) :: !glos
          end
        end
      done
    with
    | _ -> ())

  (* **********function to get all functions in the program *)
  let get_functions prog = (*C4B-FUNC *)
    (try
      let procs = ((Swig.invoke prog) "procedures_vector" Swig.C_void) in
      (* Try to get all procs for the project, get interesting info *)
      (* Search "create_cs_xxprocedure_from_ptr" in cs.ml for a decl and list of available methods *)
      let num_procs = (Swig.get_int ((Swig.invoke procs) "size" Swig.C_void)) in
      (* For each procedure, create a temporary function. *)
      for i = 0 to (num_procs - 1) do
    let proc = ((Swig.invoke procs) "[]" (Swig.C_int i)) in
        let proc_name = (Swig.get_string ((Swig.invoke proc) "name" Swig.C_void)) in  (*C4B-FNAME*)
    if proc_name <> "assert" && proc_name <> "#System_Initialization" then begin
      let args = get_funargs proc in
      let locs = get_locals proc args in
      let start_funct = !temp_func in
      let funct = {start_funct with fname=proc_name; fargs=args; flocs=locs} in
      procs_lst := !procs_lst @ [funct];
    end
      done;
      for j = 0 to (num_procs - 1) do
      (* For each procedure - translate it to a intermediate func desc *)
        let proc = ((Swig.invoke procs) "[]" (Swig.C_int j)) in
        let proc_name = (Swig.get_string ((Swig.invoke proc) "name" Swig.C_void)) in
        let ps = ((Swig.invoke proc) "get_symbol" (Swig.C_void)) in
        let attr = ((Swig.invoke ps) "get_func_attrs" (Swig.C_void)) in
        (* Check to see if the function is the main function *)
        let main_attr = Cs._func_attrs_MAIN(Swig.C_void) in
        let comp = Swig.get_bool ((Swig.invoke attr) "==" (main_attr)) in
        if proc_name <> "assert" && proc_name <> "#System_Initialization" then begin
    (* Try to get some IR elements *)
    (try
          (try
      let proc_entry_bb = ((Swig.invoke proc) "entry_basic_block" (Swig.C_void)) in
      let proc_entry_first_point = ((Swig.invoke proc_entry_bb) "first_point" (Swig.C_void)) in
          let cur_funct = List.find (fun x -> x.fname = proc_name) !procs_lst in
          let f_locs = cur_funct.flocs in
          let return_var = (match (List.filter (fun elt -> match elt with Var(elt_string, typ) ->
                                                                                                  let name_l = String.length elt_string in
                                                                                                  if name_l > 7 then begin
                                                                                                    let start_value = name_l - 7 in
                                                                                                    let sub_ret = String.sub elt_string start_value 7 in
                                                                                                    (String.compare sub_ret "$return") = 0
                                                                                                  end else false
                               | _ -> false) f_locs) with
              ret_var :: _ -> Some(ret_var)
              | [] -> None) in
      cur_args := cur_funct.fargs;
      cur_locs := f_locs;
      let block_list = get_blocks proc_entry_first_point return_var [] in
      let blocks = Array.of_list block_list in
          if (comp) then begin
              let entry_block = Array.get blocks 0 in
              let new_inst = Assign(LVal(Var("bytecodecost",Int(4))),LVal(Constant(0,4))) in
              let inst_list = entry_block.binsts in
              let updated_binsts = new_inst :: inst_list in
              let new_entry_block = {entry_block with binsts=updated_binsts} in
              Array.set blocks 0 new_entry_block;
          end;
      let updated_list = List.filter (fun y -> y.fname <> proc_name) !procs_lst in
      let funct = (if (Array.length blocks > 0) then begin
        {cur_funct with fbody=blocks; flocs = !cur_locs; fret = return_var} end else begin
        {cur_funct with flocs = !cur_locs; fret = return_var} end) in
      procs_lst := updated_list @ [funct];
      if (comp) then begin
          main := funct;
      end
        with
        | _ -> let updated_list = List.filter (fun y -> y.fname <> proc_name) !procs_lst in
               procs_lst := updated_list;);
        with
        | _ -> ());
        end
      done
    with
    | _ -> Printf.printf "    ***Failure getting procedures\n") ;;

  (*Main driver code*)
  let convert_cs () =
    let prog = Cs._project_current(Swig.C_void) in
    let c_vector = ((Swig.invoke prog) "compunits_vector" (Swig.C_void)) in
    let c_size = (Swig.get_int ((Swig.invoke c_vector) "size" (Swig.C_void))) in
    for n = 0 to (c_size - 1) do
      let c_unit = ((Swig.invoke c_vector) "[]" (Swig.C_int n)) in
      update_glos c_unit
    done ;
    get_functions prog


  let get_funcs () = !procs_lst

  let get_globs () = !glos

  let get_main () = !main


let print_bop oc op =
  match op with
  | Add -> Printf.fprintf oc " + "
  | Sub -> Printf.fprintf oc " - "
  | Mult -> Printf.fprintf oc " * "
  | Div -> Printf.fprintf oc " / "
  | Rem -> Printf.fprintf oc " Mod "
  | LShift -> Printf.fprintf oc " << "
  | RShift -> Printf.fprintf oc " >> "
  | BXor -> Printf.fprintf oc " ^ "
  | BAnd -> Printf.fprintf oc " & "
  | BOr -> Printf.fprintf oc " | "

let print_var oc x =
  match x with
    | Var(n,Array(_)) -> Printf.fprintf oc "%s[] " n
    | Var(n,_) -> Printf.fprintf oc "%s " n
    | Constant(v,s) -> Printf.fprintf oc "%d " v

let rec print_lsum oc lsum =
  match lsum with
    LExpr(l,binop,r) -> print_lsum oc l; print_bop oc binop; print_lsum oc r
  | UNeg(v) -> Printf.fprintf oc "-"; print_lsum oc v
  | LVal(v) -> print_var oc v
  | ArrayAccess(v,i) -> print_var oc v; Printf.fprintf oc "["; print_lsum oc i; Printf.fprintf oc "]"
  | LNeg(v) -> Printf.fprintf oc "!"; print_lsum oc v
  | Havoc -> Printf.fprintf oc "*"

let print_cop oc comp =
  match comp with
    GTE -> Printf.fprintf oc " >= "
  | GT -> Printf.fprintf oc " > "
  | LTE -> Printf.fprintf oc " <= "
  | LT -> Printf.fprintf oc " < "
  | NE -> Printf.fprintf oc " ~= "
  | EQ -> Printf.fprintf oc " == "

let print_cond oc cond =
  match cond with
    | Cond(lsum,comp,rsum) -> print_lsum oc lsum; print_cop oc comp; print_lsum oc rsum
    | _ -> Printf.fprintf oc ""

let print_inst oc inst =
  match inst with
    | Tick(v,r) -> Printf.fprintf oc "Tick: "; print_lsum oc r; Printf.fprintf oc "\n"
    | Assert(cond,str) -> Printf.fprintf oc "Assert: %s" str; Printf.fprintf oc "\n"
    | Assume(cond) -> Printf.fprintf oc "Assume: "; print_cond oc cond; Printf.fprintf oc "\n"
    | BinExpr(a,b,bop,c) -> print_lsum oc a; Printf.fprintf oc " = "; print_lsum oc b; print_bop oc bop; print_lsum oc c; Printf.fprintf oc "\n"
    | Assign(x,y) -> print_lsum oc x; Printf.fprintf oc " = "; print_lsum oc y; Printf.fprintf oc "\n"
    | Call(ret,callee,args) -> (match ret with
                                  | Some(v) -> (print_lsum oc v); Printf.fprintf oc " = "
                                  | None -> Printf.fprintf oc "");
                                Printf.fprintf oc "%s: " callee; List.iter (print_lsum oc) args; Printf.fprintf oc "\n"

let print_blk oc blk =
  Printf.fprintf oc "Preds: \n";
  List.iter (Printf.fprintf oc "%d ") blk.bpreds;
  Printf.fprintf oc "\n";
  List.iter (print_inst oc) blk.binsts;
  let etype = blk.btype in
  match etype with
      Return(Some(ret_var)) -> Printf.fprintf oc "Ret: "; (print_var oc) ret_var; Printf.fprintf oc "\n"
    | Return(None) -> Printf.fprintf oc "Ret: <void>\n"
    | Branch(children) -> (
      let cond = blk.bcond in
      match cond with
        Some(NonDet) -> Printf.fprintf oc "If (*): "; List.iter (Printf.fprintf oc "b%d ") children; Printf.fprintf oc "\n"
      | Some(Jmp) -> Printf.fprintf oc "Jmp: "; List.iter (Printf.fprintf oc "b%d ") children; Printf.fprintf oc "\n"
      | Some(c) -> Printf.fprintf oc "If ("; (print_cond oc c); Printf.fprintf oc ") b%d " (List.hd children); Printf.fprintf oc "else b%d\n" (List.hd (List.tl  children))
      | None -> Printf.fprintf oc "ncond: "; List.iter (Printf.fprintf oc "b%d ") children
    )


let print_fn oc f =
  Printf.fprintf oc "\n";
  Printf.fprintf oc "FName: %s\n" f.fname;
  Printf.fprintf oc "Locs: \n";
  List.iter (print_var oc) f.flocs;
  Printf.fprintf oc "\n";
  Printf.fprintf oc "Args: \n";
  List.iter (print_var oc) f.fargs;
  Printf.fprintf oc "\n";
  let num_blks = Array.length f.fbody in
  for b = 0 to num_blks - 1 do
    let cur_blk = Array.get f.fbody b in
    Printf.fprintf oc "b%d:\n" b;
    (print_blk oc) cur_blk
  done

let print_functions oc =
  Printf.fprintf oc "Globs: \n";
  List.iter (print_var oc) !glos;
  Printf.fprintf oc "\n";
  List.iter (print_fn oc) !procs_lst
