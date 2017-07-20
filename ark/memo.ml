module Make (M : Hashtbl.HashedType) : sig
  val memo : ?size:int -> (M.t -> 'a) -> (M.t -> 'a)
  val memo_recursive: ?size:int -> ((M.t -> 'a) -> M.t -> 'a) -> (M.t -> 'a)
end = struct
  module HT = Hashtbl.Make(M)
  let memo ?size:(size=991) f =
    let memo_table = HT.create size in
    fun x -> (try HT.find memo_table x
              with Not_found ->
                let result = f x in
                HT.add memo_table x result;
                result)
  let memo_recursive ?size:(size=991) f =
    let memo_table = HT.create size in
    let rec g x =
      (try HT.find memo_table x
       with Not_found ->
         let result = f g x in
         HT.add memo_table x result;
         result)
    in
    g
end

(** Memoize a function using built-in polymorphic hash *)
let memo ?size:(size=991) f =
  let memo_table = Hashtbl.create size in
  fun x -> (try Hashtbl.find memo_table x
            with Not_found ->
              let result = f x in
              Hashtbl.add memo_table x result;
              result)

let memo_recursive ?size:(size=991) f =
  let memo_table = Hashtbl.create size in
  let rec g x =
    (try Hashtbl.find memo_table x
     with Not_found ->
       let result = f g x in
       Hashtbl.add memo_table x result;
       result)
  in
  g


module Tabulate = struct

  module type Fun = sig
    type dom
    type cod

    (** Function to be tabulated *)
    val f : dom -> (cod -> unit) -> unit
    val hash : dom -> int
    val join : cod -> cod -> cod
    val bottom : cod
    val dom_equal : dom -> dom -> bool
    val cod_equal : cod -> cod -> bool
  end

  module type S = sig
    type dom
    type cod
    val update : dom -> cod -> unit
    val call : dom -> (cod -> unit) -> unit
    val call_direct : dom -> cod
  end

  (** Similar to {!memo_recursive}, but also works when recursion is not
      well-founded (the result of f x depends on f x).  In this case, the least
      fixpoint of {!f} is computed.  This requires a join semilattice structure
      of the codomain of {!f} and for the overall system of inequations defining
      {!f} to be monotone.  {!f} must be written in continuation passing style;
      the return continuation will be called repeatedly during fixpoint
      computation. *)
  module Make (F : Fun) : S with type dom = F.dom
                             and type cod = F.cod =
  struct
    module H = Hashtbl.Make(struct
        type t = F.dom
        let hash = F.hash
        let equal = F.dom_equal
      end)
    type dom = F.dom
    type cod = F.cod
    let value  = H.create 991
    let depend = H.create 991 (* Track a list of continuations for each table
                                 				 entry (the continuations passed to call). *)

    let update x new_value =
      let old = H.find value x in
      let cur = F.join old new_value in
      if not (F.cod_equal old cur) then begin
        H.replace value x cur;
        List.iter (fun k -> k cur) (H.find depend x)
      end

    let call x k =
      let v =
        try H.find value x
        with Not_found ->
          H.add value x F.bottom;
          H.add depend x [];
          F.f x (update x);
          H.find value x
      in
      H.replace depend x (k::(H.find depend x));
      k v

    let call_direct x =
      try H.find value x
      with Not_found ->
        let result = ref F.bottom in
        let k r = result := r in
        F.f x k;
        !result
  end

  module type RecFun = sig
    type dom
    type cod

    (** Function to be tabulated *)
    val f : (dom -> (cod -> unit) -> unit) -> dom -> (cod -> unit) -> unit
    val hash : dom -> int
    val join : cod -> cod -> cod
    val bottom : cod
    val dom_equal : dom -> dom -> bool
    val cod_equal : cod -> cod -> bool
  end

  module MakeRec (F : RecFun) : S with type dom = F.dom
                                   and type cod = F.cod =
  struct
    module rec Fun : Fun with type dom = F.dom
                          and type cod = F.cod =
    struct
      include F
      let f = F.f Tab.call
    end

    and Tab : S with type dom = F.dom
                 and type cod = F.cod = Make(Fun)

    include Tab
  end
end
