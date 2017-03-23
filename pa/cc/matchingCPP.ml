open Pervasives
open BatPervasives
open Apak

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
end

module Make (Predicate : Symbol) = struct
  type predicate = Predicate.t
  type str = (int * (predicate * int list) list)
  type t = { str1 : str;
             str2 : str}

  let empty = { str1 = (0, []);
                str2 = (0, []) }

  (* Just store this in a nice way to pass to C *)
  let make univ1 props1 univ2 probs2 =
    let make_list str = BatRefList.to_list (BatRefList.of_enum str) in
    { str1 = (univ1, make_list props1);
      str2 = (univ2, make_list probs2)}

  (* The actual call to the c function *)
  external embedsCPP : str -> str ->  bool = "embedsOCAML"

  (* Uncouple record *)
  let embeds embedding = embedsCPP embedding.str1 embedding.str2

end
