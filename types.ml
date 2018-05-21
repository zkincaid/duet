(*
type expr = 
          | Plus of expr * expr     (** Binary addition *)
          | Times of expr * expr    (** Binary multiplication *)
          | Minus of expr * expr    (** Binary subtraction *)
          | Divide of expr * expr   (** Binary division *)
          | Product of expr list    (** N-ary multiplication *)
                        (* want these two for flattening AST not indexed sums and products *)
          | Sum of expr list        (** N-ary addition *)
          | Symbolic_Constant of string (** "x", "y", etc *)
          | Base_case of string * int   (** y_0, y_1, ... *)
          | Output_variable of string * subscript (** y_n, y_n+1, y_n+2, ... *)
          | Input_variable of string    (** Index variable *)
          (* Maybe just make everything floats? *)
          | Rational of Mpq.t       (** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpq.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)
          | Log of Mpq.t *  expr    (** Base b log *)
          | Pow of expr * expr      (** Binary exponentiation *)
          | Binomial of expr * expr (** Binomial coeffiecient *)
          | IDivide of expr * Mpq.t (** Integer Division *)
          | Sin of expr         (** Trigonometric sine *)
          | Cos of expr         (** Trigonometric cosine *)
          | Arctan of Mpq.t     (** Inverse tangent function *)
          | Mod of expr * expr      (** Modular expression *)
          | Pi              (** The trancendental number pi *)
          | Factorial of expr       (** Factorial *)
          | Iif of string * subscript   (** Impliciltly intrepreted function *)
          | Shift of int * expr     (** first argument represents amount to shift by. Neg ints represent left shifts *)
          | Undefined           (** An expression whose value is undefined. ie x/0, log(-1), etc *)
          ;;


type inequation = Equals of expr * expr   (** = *)
(*        | LessEq of expr * expr         (** <= *)
          | Less of expr * expr           (** < *)
          | GreaterEq of expr * expr      (** >= *)
          | Greater of expr * expr        (** > *)
*)
          ;;
*)


