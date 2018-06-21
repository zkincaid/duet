open Graph;;

(* ------------------------------------------------------------------------- *)

type subscript = 
          | SAdd of string * int    (** n+1, n+2, ... *)
          | SSVar of string;;       (** n *)

type expr = 
          | Product of expr list    (** N-ary multiplication *)
          | Sum of expr list        (** N-ary addition *)
          | Max of expr list        (** N-ary max *)
          | Min of expr list        (** N-ary min *)
          | Base_case of string * int   (** y_0, y_1, ... *)
          | Output_variable of string * subscript (** y_n, y_n+1, y_n+2, ... *)
          | Input_variable of string    (** Index variable *)
          | Rational of Mpq.t;; 

type inequation = 
          | Equals of expr * expr
          | LessEq of expr * expr
          | GreaterEq of expr * expr;;

(* John suggested the following URL for documentation of Mpq and the rest of GMP:
http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpq.html *)

(* ------------------------------------------------------------------------- *)

(* Finite weights: *)
type fweight = Mpq.t;;
(* Possibly-infinite weights: *)
type weight = Inf | Fin of fweight;;

let fwt_add x y = 
    let retval = Mpq.init () in
    let _ = Mpq.add retval x y in
    retval;;
let fwt_sub x y =
    let retval = Mpq.init () in
    let _ = Mpq.sub retval x y in
    retval;;
let fwt_div x y =
    let retval = Mpq.init () in
    let _ = Mpq.div retval x y in
    retval;;
let fwt_from_int i = 
    let retval = Mpq.init () in 
    let _ = Mpq.set_si retval i 1 in
    retval;;
let fwt_zero = (* Should this be a function taking () ? *)
    let retval = Mpq.init () in 
    (* let _ = Mpq.set_si retval 0 0 in *)
    retval;;
let fwt_is_zero fwt = if Mpq.sgn fwt = 0 then true else false;; (*convenience*)
let fwt_is_one fwt = if Mpq.cmp_si fwt 1 1 = 0 then true else false;; (*convenience*)
let fwt_neg fwt = 
    let retval = Mpq.init () in
    Mpq.neg retval fwt;
    retval;;

(* ------------------------------------------------------------------------- *)

module V = struct
  type t = int (* vertex number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;
module E = struct
  type t = fweight
  let compare = Pervasives.compare
  let default = fwt_zero
end;;

(* Max-plus recurrence graph *)
module MPGraph = Imperative.Digraph.ConcreteLabeled(V)(E);;

module V2 = struct
  type t = int (* SCC number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;

module SCCGraph = Imperative.Digraph.Concrete(V2);;

module MPComponents = Graph.Components.Make(MPGraph);;

module SCCOper = Graph.Oper.I(SCCGraph);;

module IntMap = Map.Make(struct type t = int let compare = compare end);;
module IntIntMap = Map.Make(struct type t = int * int let compare = compare end);;

