module type PLUGIN =
  sig
    val main: string list -> unit
  end

let p = ref None
let get_plugin () : (module PLUGIN)  =
    match !p with
    | Some s -> s
    | None -> failwith "No plugin loaded"
