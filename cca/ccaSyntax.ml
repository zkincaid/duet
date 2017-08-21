open Ark
open Syntax

module Ctx = Syntax.MakeSimplifyingContext ()
include Ctx

include Log.Make(struct let name = "CcaSyntax" end)

module Var = struct
  type t = string

  let show x = x
  let pp = Format.pp_print_string
  let compare = Pervasives.compare

  let sym_to_var = Hashtbl.create 991
  let var_to_sym = Hashtbl.create 991

  let typ _ = `TyInt

  let symbol_of var =
    if Hashtbl.mem var_to_sym var then
      Hashtbl.find var_to_sym var
    else begin
      let sym = Ctx.mk_symbol ~name:(show var) (typ var) in
      Hashtbl.add var_to_sym var sym;
      Hashtbl.add sym_to_var sym var;
      sym
    end

  let of_symbol sym =
    if Hashtbl.mem sym_to_var sym then
      Some (Hashtbl.find sym_to_var sym)
    else
      None
end

module Tr = struct
  include Transition.Make(Ctx)(Var)
  let default = one
end

(* cost equation systems *)
type ces =
  { start : string;
    rules : (((string * string list) * (string * term list) * formula) list) }

(* ITS vertices *)
module V = struct
  type t = string
  let equal = (=)
  let hash = Hashtbl.hash
  let compare = Pervasives.compare
end

(* Integer Transition Systems *)
module ITS = Graph.Persistent.Digraph.ConcreteLabeled(V)(Tr)

module DisplayITS = Apak.ExtGraph.Display.MakeLabeled
    (ITS)
    (struct
      type t = string
      let pp = Format.pp_print_string
    end)
    (struct
      type t = Tr.t
      let pp = Tr.pp
    end)

let cost = Var.symbol_of "cost"

let its_of_ces ces =
  List.fold_left (fun g ((src,src_args),(dst,dst_args), guard) ->
      let assignment =
        List.fold_right2 (fun s d args -> (s,d)::args) src_args dst_args
          [("cost", Ctx.mk_add [Ctx.mk_const cost; Ctx.mk_real QQ.one])]
      in
      let tr = Tr.construct guard assignment in
      let edge = ITS.E.create src tr dst in
      let g = ITS.add_vertex g src in
      let g = ITS.add_vertex g dst in
      ITS.add_edge_e g edge)
    (ITS.add_vertex ITS.empty ces.start)
    ces.rules
