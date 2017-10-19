open Pervasives
open BatPervasives
open Ark

include Log.Make(struct let name = "MatchingCPP" end)

module type Symbol = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type t
  type predicate

  (* empty embedding problem *)
  val empty : t

  (* prepare embedding problem to be passed to C / C++ *)
  val make : int -> (predicate * int list) BatEnum.t -> int -> (predicate * int list) BatEnum.t -> t

  (* run the embedding problem in C / C++ *)
  val embeds : t -> bool
  val uembeds : t -> bool
  val cembeds : t -> bool
  val emb2mzn : t -> bool
  val haifacsp : t -> bool
  val ortools : t -> bool
end

module Make (Predicate : Symbol) = struct
  type predicate = Predicate.t
  type str = (int * (int * int list) list)
  type t = { str1 : str;
             str2 : str}

  let empty = { str1 = (0, []);
                str2 = (0, []) }

  module M = Memo.Make(Predicate)
  (* Just store this in a nice way to pass to C *)
  let make univ1 props1 univ2 probs2 =
    let max_id = ref (-1) in
    let rename = M.memo (fun p -> incr max_id; !max_id) in
    let make_list str =
      BatEnum.fold (fun tl (p, args) -> (rename p, args) :: tl) [] str
    in
    { str1 = (univ1, make_list props1);
      str2 = (univ2, make_list probs2)}

  (* The actual call to the c function *)
  external embedsCPP : str -> str -> int ->  bool = "embedsOCAML"

  (* Uncouple record *)
  let uembeds embedding = embedsCPP embedding.str1 embedding.str2 0

  let embeds embedding = embedsCPP embedding.str1 embedding.str2 1

  let cembeds embedding = embedsCPP embedding.str1 embedding.str2 2

  let emb2mzn embedding = embedsCPP embedding.str1 embedding.str2 3

  let haifacsp embedding = embedsCPP embedding.str1 embedding.str2 4

  let ortools embedding = embedsCPP embedding.str1 embedding.str2 5
end
