(*
   Print a tree or a DAG as tree, similarly to the 'tree' command.
   Source: https://gist.github.com/mjambon/75f54d3c9f1a352b38a8eab81880a735
*)

val to_buffer :
  ?line_prefix: string ->
  get_name: ('a -> string) ->
  get_children: ('a -> 'a list) ->
  Buffer.t -> 'a -> unit

val to_string :
  ?line_prefix: string ->
  get_name: ('a -> string) ->
  get_children: ('a -> 'a list) ->
  'a -> string