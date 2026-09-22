(** Polynomial ideals. *)
  type t

  (** Pretty print *)
  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  (** Compute the smallest ideal that contains a given set of polynomials *)
  val make : Polynomial.QQXs.t list -> t

  val add_saturate : t -> Polynomial.QQXs.t -> t

  val reduce : t -> Polynomial.QQXs.t -> Polynomial.QQXs.t

  (** Compute a finite set of polynomials that generates the given
     ideal.  Note [make (generators i) = i], but [generators (make g)]
     is not necessarily equal to [g]. *)
  val generators : t -> Polynomial.QQXs.t list

  (** Is one ideal contained inside another? *)
  val subset : t -> t -> bool

  (** Is one ideal equal to another? *)
  val equal : t -> t -> bool

  (** Does an ideal contain a given polynomial? *)
  val mem : Polynomial.QQXs.t -> t -> bool

  (** Intersect two ideals. *)
  val intersect : t -> t -> t

  (** Compute the ideal consisting of all products of polynomials
     belonging to the two given ideals *)
  val product : t -> t -> t

  (** Compute the ideal consisting of all sums of polynomials beloning
     to the two given ideals *)
  val sum : t -> t -> t

  (** Compute the ideal consisting of all polynomials in the given
     ideal that are defined only over dimensions satisfying the given
     predicate. *)
  val project : (int -> bool) -> t -> t

  (** Make a rewrite system from the given ideal.*)
  val mk_rewrite : t -> Polynomial.Rewrite.t
