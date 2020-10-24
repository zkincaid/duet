(*************************************************************************
  The types below describe the AST of Smtlib2 responses
  for the get-model command.

  The types defined below follow exactly from the concrete
  syntax provided by Smtlib2 version 2.6 e.g. from
  http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
 *************************************************************************)
type constant =
  | Int of ZZ.t
  | Real of QQ.t
  | String of string

type symbol = string

type index =
  | Num of ZZ.t
  | Sym of symbol

(* identifiers are names given to things within Smtlib2
   most commonly used to denote functions and sorts.
   identifiers come in two varieties simple and indexed.

   A simple identifier will have an empty list of indexes
   and would correspond to names like "Real" or "plus" or "+"

   An indexed identifier will have a non-empty list of indexes
   and represents more complex sorts/names e.g.
   "(_ BitVec 32)" or "(_ move up)" *)
type identifier = symbol * (index list)

(* this is the type of possibly parametric sorts
   e.g. "Bool", "Real", or "(Set (Bool))" *)
type sort = Sort of identifier * (sort list)

(* a possibly sorted identifier *)
type qual_id = identifier * (sort option)

(* a match pattern, e.g.
   "Nil", "(Cons hd Nil)", "(Cons hd tl)" *)
type pattern = symbol * (symbol list)

(* attribute values can be a general sexpr as defined below *)
type sexpr =
  | SConst of constant
  | SSym of symbol
  | SKey of symbol
  | SSexpr of sexpr list

(* value of atributes *)
type attribute_value =
  | VConst of constant
  | VSym of symbol
  | VSexpr of sexpr list

(* an attribute is a keyword with an optional value
   e.g. ":named" or ":print-term true" *)
type attribute = symbol * (attribute_value option)

(* an Smtlib2 term, similar to a Srk expression *)
type term =
  | Const of constant
  | App of qual_id * (term list)
  | Let of ((symbol * term) list) * term
  | Forall of ((symbol * sort) list) * term
  | Exists of ((symbol * sort) list) * term
  | Match of term * (match_case list)
  | Attribute of term * (attribute list)
and match_case = pattern * term

(* an Smtlib2 model, a list of symbols paired with thier
   (possibly mutually recursively defined) definitions *)
type model = (symbol * ((symbol * sort) list) * sort * term) list
