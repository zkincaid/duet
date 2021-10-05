open Syntax

module OldPmfa : sig
  open Iteration
  module V = Linear.QQVector
  module M = Linear.QQMatrix
  module Z = Linear.ZZVector
  module T = TransitionFormula
  val pmfa_to_lia : 'a context -> 'a T.t -> 'a T.t

  val eliminate_stores : 'a context -> 'a formula -> 'a formula

  val unbooleanize : 'a context -> 'a formula -> 'a formula

  (* [projection srk tf] returns [(j, j', map, tf')] where [tf'] is a
   * projection of the transition formula [tf] such that for any array
   * transition relation [(a, a')] in [tf], the dynamics of [(a, a')] are
   * projected to just their contents at symbolic index [j], captured by the
   * transition relation [(map a, map a')] of [tf'].*) 
  val projection :  
    'a context -> 'a T.t -> symbol * symbol * (symbol, symbol) Hashtbl.t * 'a T.t

  module Array_analysis (Iter : PreDomain) : sig
    include PreDomain
  end
end
