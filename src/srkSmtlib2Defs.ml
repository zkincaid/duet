type constant =
  | Int of ZZ.t
  | Real of QQ.t
  | String of string

type symbol = string

type index =
  | Num of ZZ.t
  | Sym of symbol

type identifier = symbol * (index list)

type sort = Sort of identifier * (sort list)

type qual_id = identifier * (sort option)

type pattern = symbol * (symbol list)

type sexpr =
  | SConst of constant
  | SSym of symbol
  | SKey of symbol
  | SSexpr of sexpr list

type attribute_value =
  | VConst of constant
  | VSym of symbol
  | VSexpr of sexpr list

type attribute = symbol * (attribute_value option)

type term =
  | Const of constant
  | App of qual_id * (term list)
  | Let of ((symbol * term) list) * term
  | Forall of ((symbol * sort) list) * term
  | Exists of ((symbol * sort) list) * term
  | Match of term * (match_case list)
  | Attribute of term * (attribute list)
and match_case = pattern * term

type model = (symbol * ((symbol * sort) list) * sort * term) list
