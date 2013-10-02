type goto_program
type goto_function
type irep
type goto_symbol
type goto_instr
type goto_instr_type =
  | GNoInstructionType
  | GGoto              (** branch, possibly guarded *)
  | GAssume	       (** non-failing guarded self loop *)
  | GAssert	       (** assertions *)
  | GOther	       (** anything else *)
  | GSkip	       (** just advance the PC *)
  | GStartThread       (** spawns an asynchronous thread *)
  | GEndThread	       (** end the current thread *)
  | GLocation	       (** semantically like SKIP *)
  | GEndFunction       (** exit point of a function *)
  | GAtomicBegin       (** marks a block without interleavings *)
  | GAtomicEnd	       (** end of a block without interleavings *)
  | GReturn            (** return from a function *)
  | GAssign	       (** assignment lhs:=rhs *)
  | GDecl	       (** declare a local variable *)
  | GDead	       (** marks the end-of-live of a local variable *)
  | GFunctionCall      (** call a function *)
  | GThrow	       (** throw an exception *)
  | GCatch	       (** catch an exception *)		

external read_binary : string -> goto_program = "wrapper_read_binary"
external irep_find : irep -> string -> irep = "wrapper_irep_find"
external irep_find_string : irep -> string -> string =
    "wrapper_irep_find_string"
external irep_id : irep -> string = "wrapper_irep_string"
external irep_arguments : irep -> irep list = "wrapper_irep_arguments"
external irep_components : irep -> irep list = "wrapper_irep_components"
external irep_operands : irep -> irep list = "wrapper_irep_operands"
external instr_type : goto_instr -> goto_instr_type = "wrapper_instr_type"
external instr_guard : goto_instr -> irep = "wrapper_instr_guard"
external instr_operands : goto_instr -> irep list = "wrapper_instr_operands"
external instr_successors : goto_function -> goto_instr -> goto_instr list =
    "wrapper_instr_successors"
external instr_location : goto_instr -> irep = "wrapper_instr_location"
external print_instr : goto_instr -> unit = "wrapper_print_instr"
external print_irep : irep -> unit = "wrapper_print_irep"

external symbol_static_lifetime : goto_symbol -> bool =
    "wrapper_symbol_static_lifetime"
external symbol_is_extern : goto_symbol -> bool = "wrapper_symbol_is_extern"
external symbol_base_name : goto_symbol -> string = "wrapper_symbol_base_name"
external symbol_type : goto_symbol -> irep = "wrapper_symbol_type"
external symbol_value : goto_symbol -> irep = "wrapper_symbol_value"
external symbol_location : goto_symbol -> irep = "wrapper_symbol_location"
external symbol_is_lvalue : goto_symbol -> bool = "wrapper_symbol_is_lvalue"
external symbol_is_type : goto_symbol -> bool = "wrapper_symbol_is_type"
external symbol_is_macro : goto_symbol -> bool = "wrapper_symbol_is_macro"
external print_symbol : goto_symbol -> unit = "wrapper_print_symbol"

val iter_functions : (string -> goto_function -> unit) -> goto_program -> unit
val iter_instr : (goto_instr -> unit) -> goto_function -> unit
val iter_symbol : (string -> goto_symbol -> unit) -> goto_program -> unit
