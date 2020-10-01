module Make (M : Hashtbl.HashedType) = struct
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

module MakeWeak(M : Hashtbl.HashedType) = struct 
  (* module for weak hashtbl:
     Ephemeron.K1 is a Key Value pair
     The key is weak (as in the Weak module)
     The value is considered alive while the key is alive. *)
  module WHT = Ephemeron.K1.Make(M)
  let memo ?size:(size=991) f =
    let memo_table = WHT.create size in
    fun x -> (try WHT.find memo_table x
              with Not_found ->
                let result = f x in
                WHT.add memo_table x result;
                result)
    let memo_recursive ?size:(size=991) f =
      let memo_table = WHT.create size in
      let rec g x =
        (try WHT.find memo_table x
         with Not_found ->
           let result = f g x in
           WHT.add memo_table x result;
           result)
      in
      g
end

(* Default cache params *)
let default_params : Cache.cache_params = {
  max_size = 1000;     (* trigger first resize/eviction when the 1001st element is added *)
  hard_limit = 0;      (* can grow unboundedly if enough keys are used frequently enough *)
  keys_hit_rate = 0.9; (* grow if 90% of keys are used within last two resize decisions *)
  min_hits = 0.9;      (*    or if they were used very fequently in the past *)
  aging_factor = 0.95; (* exponential decaying factor -- recent hits are worth more than older hits *)
}

module MakeCache(C : Cache.S) = struct
  let memo ?(params = default_params) ?(size=991) f =
    let memo_table = C.create ~params size in
    fun x -> (try C.find memo_table x
              with Not_found ->
                let result = f x in
                C.add memo_table x result;
                result)

  let memo_recursive ?(params = default_params) ?(size = 991) f =
    let memo_table = C.create ~params size in
    let rec g x =
      (try C.find memo_table x
       with Not_found ->
         let result = f g x in
         C.add memo_table x result;
         result)
    in
    g
end

module MakeCacheHF(C : Cache.HashS) = struct
  let memo ?(params = default_params) ?(size=991) f =
    let memo_table = C.create ~params size in
    fun x -> (try C.find memo_table x
              with Not_found ->
                let result = f x in
                C.add memo_table x result;
                result)

  let memo_recursive ?(params = default_params) ?(size = 991) f =
    let memo_table = C.create ~params size in
    let rec g x =
      (try C.find memo_table x
       with Not_found ->
         let result = f g x in
         C.add memo_table x result;
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

module LRUMemo = MakeCache(Cache.LRU)
let lru_memo = LRUMemo.memo
let lru_memo_recursive = LRUMemo.memo_recursive

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
