open Duet_plugin

module M:Plugin_interface.PLUGIN =
  struct
    let main args =
        match (List.nth args 0) with
          | "-query" -> Duet_init.duet_main ();
          | _ -> ()
  end

let () =
 Plugin_interface.p := Some (module M:Plugin_interface.PLUGIN)

