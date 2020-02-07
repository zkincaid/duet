(** Sparse, flow-sensitive, field-sensitive pointer analysis *)
open Core
open Apak
open PointerAnalysis

(* Convert a set of memory location to a map from memory base addresses to
   sets of offsets *)
let mk_map set =
  let add (base, offset) map =
    let offsets =
      if MemBase.Map.mem base map
      then Offset.Set.add offset (MemBase.Map.find base map)
      else Offset.Set.singleton offset
    in
    MemBase.Map.add base offsets map
  in
  MemLoc.Set.fold add set MemBase.Map.empty

module Domain = struct
  module S = struct
    include Lattice.Bounded.LiftSubset(MemLoc.Set)
    let join x y = match x, y with
      | (Set a, Set b) ->
        let memloc_set = MemLoc.Set.union a b in
        let f (base,offset) =
          offset = OffsetUnknown
          || not (MemLoc.Set.mem (base, OffsetUnknown) memloc_set)
        in
        Set (MemLoc.Set.filter f memloc_set)
      | (_, _) -> Neg (MemLoc.Set.empty)
  end
  module FS = Lattice.FunctionSpace.Total.Make(AP)(S)
  include FS
  let project f aps =
    AP.Set.fold (fun ap g -> update ap (eval f ap) g) aps (const (default f))
  let inject f _ = f
  let cyl f aps = AP.Set.fold (fun ap g -> update ap S.top g) aps f

  let rename f rename =
    let rename = List.filter (fun (x,y) -> not (AP.equal x y)) rename in
    let left =
      List.fold_left (fun s x -> AP.Set.add (fst x) s) AP.Set.empty rename
    in
    let right =
      List.fold_left (fun s x -> AP.Set.add (snd x) s) AP.Set.empty rename
    in
    let rename_one g (x, y) = update y (eval f x) g in
    let remove = AP.Set.diff left right in
    cyl (List.fold_left rename_one f rename) remove

  let is_bottom = FS.equal (const S.bottom)
  let top _ = const S.top
  let bottom _ = const S.bottom

  module E = MakeEval(
    struct
      type t = MemLoc.Set.t
      let change_offset f =
        let change = function
          | (rhs, OffsetFixed off) -> (rhs, f off)
          | x -> x
        in
        MemLoc.Set.map change
      let join = MemLoc.Set.union
      let havoc = MemLoc.Set.empty
      let addr_of v = MemLoc.Set.singleton (MAddr (fst v), snd v)
      let str_const str = MemLoc.Set.singleton (MStr str, OffsetFixed 0)
    end)

  let transfer def points_to =
    let env ap = match FS.eval points_to ap with
      | S.Set mem -> mem
      | S.Neg _ -> MemLoc.Set.empty
    in
    begin match def.dkind with
      | Store (ap, expr) ->
        begin match E.eval expr env with
          | VConst _ -> FS.update ap (S.Set MemLoc.Set.empty) points_to
          | VRhs mem -> FS.update ap (S.Set mem) points_to
        end
      | Assign (var, expr) ->
        begin
          let ap = Variable var in
          match E.eval expr env with
          | VConst _ -> FS.update ap (S.Set MemLoc.Set.empty) points_to
          | VRhs mem -> FS.update ap (S.Set mem) points_to
        end
      | Builtin (Alloc (lhs, _, _)) ->
        let heaploc = (MAlloc def, OffsetFixed 0) in
        FS.update (Variable lhs) (S.Set (MemLoc.Set.singleton heaploc)) points_to
      | Initial -> FS.const S.bottom
      | Assume _ | Assert _ | AssertMemSafe _ | Call _ -> points_to
      | Return _ -> points_to
      | Builtin (Free _) -> assert false
      | Builtin (Fork _) -> points_to
      | Builtin (Acquire _) | Builtin (Release _) -> points_to
      | Builtin AtomicBegin | Builtin AtomicEnd -> points_to
      | Builtin Exit -> FS.const S.bottom
    end

  let widen_memloc_set x y =
    let x_map = mk_map x in
    let y_map = mk_map y in
    let unmap base y_offsets set =
      let x_offsets =
        try MemBase.Map.find base x_map
        with Not_found -> Offset.Set.empty
      in
      if Offset.Set.equal x_offsets y_offsets
      then begin
        Offset.Set.fold
          (fun offset set -> MemLoc.Set.add (base,offset) set)
          x_offsets
          set
      end else MemLoc.Set.add (base, OffsetUnknown) set
    in
    MemBase.Map.fold unmap y_map MemLoc.Set.empty

  let widen x y =
    let y = join x y in
    let f fs (ap, y_memlocs) =
      let x_memlocs = FS.eval x ap in
      let memlocs = match x_memlocs, y_memlocs with
        | S.Set x_memlocs, S.Set y_memlocs ->
          S.Set (widen_memloc_set x_memlocs y_memlocs)
        | _ -> S.top
      in
      FS.update ap memlocs fs
    in
    BatEnum.fold f (const S.top) (enum y)

  let assert_true _ _ = false
  let assert_memsafe _ _ = false
  let name = "Flow-sensitive pointer analysis"
end

module Solve = Solve.MakeAfgSolver(Domain)

let analyze dg =
  let state = Solve.mk_state dg in
  let f (def, value) = match def.dkind with
    | Store (lhs, _) ->
      let points_to = Domain.FS.eval value lhs in
      Format.fprintf Format.std_formatter "%a -> %a@\n"
        Def.pp def
        Domain.S.pp points_to
    | Assign (lhs, _) ->
      let points_to = Domain.FS.eval value (Variable lhs) in
      Format.fprintf Format.std_formatter "%a -> %a@\n"
        Def.pp def
        Domain.S.pp points_to
    | _ -> ()
  in
  let result = Solve.do_analysis state dg in
  BatEnum.iter f (Solve.S.enum_output result)

module S = Domain.S
let diff a b =
  let change_count = ref 0 in
  let print_plus memloc = print_endline ("+" ^ (MemLoc.show memloc)) in
  let print_minus memloc = print_endline ("-" ^ (MemLoc.show memloc)) in
  let go (def, a) =
    try
      let b = Solve.S.output b def in
      let go_ap ap =
        let a = Domain.eval a ap in
        let b = Domain.eval b ap in
        let add = Domain.S.diff a b in
        let remove = Domain.S.diff b a in
        let diff = Domain.S.union add remove in
        if not (Domain.S.equal diff (S.Set MemLoc.Set.empty))
        then begin
          incr change_count;
          print_endline ("diff @ " ^ (Def.show def)
                         ^ " ap: " ^ (AP.show ap));
          begin match add with
            | S.Set add -> MemLoc.Set.iter print_plus add
            | S.Neg _ -> print_endline "+infinity"
          end;
          begin match remove with
            | S.Set remove -> MemLoc.Set.iter print_minus remove
            | S.Neg _ -> print_endline "-infinity"
          end
        end
      in
      AP.Set.iter go_ap (Def.get_uses def)
    with _ -> Srk.Log.logf ~level:`debug "No b output at : %a" Def.pp def
  in
  BatEnum.iter go (Solve.S.enum_output a);
  print_endline ("Total diff count: " ^ (string_of_int (!change_count)))

let _ =
  let go file = analyze (AliasLogic.construct_dg file) in
  CmdLine.register_pass
    ("-fspa", go, " Flow-sensitive pointer analysis")

