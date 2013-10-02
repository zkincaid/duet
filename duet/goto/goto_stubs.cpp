#include <cstring>
#include "util/context.h"
#include "util/message.h"
#include "util/ui_message.h"
#include "goto-programs/read_goto_binary.h"
#include "goto-programs/goto_functions.h"
#include "goto-programs/goto_function_pointers.h"
#include "goto-programs/remove_unused_functions.h"
#include "goto-programs/goto_inline.h"
#include "goto-programs/string_abstraction.h"

typedef goto_functionst::goto_functiont goto_functiont;
typedef goto_programt::instructiont instructiont;
typedef std::list<instructiont>::const_iterator targett;
typedef std::pair<goto_functionst, contextt> program;

#define CAML_ASSIGN 0
#define CAML_ASSUME 1
#define CAML_ASSERT 2
#define CAML_DECL 3
#define CAML_SKIP 5
#define CAML_RETURN 6

extern "C" {

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <stdio.h>

#define Irep_val(v) (*((irept**) Data_custom_val(v)))
#define Instr_val(v) (*((targett**) Data_custom_val(v)))
#define Symbol_val(v) (*((symbolt**) Data_custom_val(v)))
#define Program_val(v) (*((program**) Data_custom_val(v)))
#define Function_val(v) (*((const goto_functiont**) Data_custom_val(v)))
#define Val_instrtype(v) (Val_int(v))

    /** irep custom operations ************************************************/
    void finalize_irep(value v) {
	//delete Irep_val(v);
    }

    int compare_irep(value v1, value v2) {
	// compare pointers
	irept *r1, *r2;
	return Irep_val(v1)->compare(*Irep_val(v2));
    }

    intnat hash_irep(value v) {
	return (intnat) Irep_val(v)->hash();
    }

    static struct custom_operations irep_ops = {
	(char*) "goto.irep",
	finalize_irep,
	compare_irep,
	hash_irep,
	custom_serialize_default,
	custom_deserialize_default
    };

    value alloc_irep(irept irep) {
	value r;
	r = alloc_custom(&irep_ops, sizeof(irept *), 0, 1);
	Irep_val(r) = new irept(irep);
	return r;
    }

    /** instr custom operations ***********************************************/
    void finalize_instr(value v) {
	//delete Instr_val(v);
    }

    int compare_instr(value v1, value v2) {
	// compare pointers
	const instructiont *r1, *r2;
	r1 = &(**Instr_val(v1));
	r2 = &(**Instr_val(v2));
	if (r1 < r2) {
	    return -1;
	} else if (r1 == r2) {
	    return 0;
	} else {
	    return 1;
	}
    }

    intnat hash_instr(value v) {
	return (intnat) &(**Instr_val(v));
    }

    static struct custom_operations instr_ops = {
	(char*) "goto.instr",
	finalize_instr,
	compare_instr,
	hash_instr,
	custom_serialize_default,
	custom_deserialize_default
    };

    value alloc_instr(targett target) {
	value r;
	r = alloc_custom(&instr_ops, sizeof(targett *), 0, 1);
	Instr_val(r) = new targett(target);
	return r;
    }

    /** symbol custom operations **********************************************/
    void finalize_symbol(value v) {
	//delete Symbol_val(v);
    }

    static struct custom_operations symbol_ops = {
	(char*) "goto.symbol",
	finalize_symbol,
	custom_compare_default,
	custom_hash_default,
	custom_serialize_default,
	custom_deserialize_default
    };

    value alloc_symbol(symbolt sym) {
	value r;
	r = alloc_custom(&symbol_ops, sizeof(symbolt *), 0, 1);
	Symbol_val(r) = new symbolt(sym);
	return r;
    }

    /** program custom operations *********************************************/
    void finalize_program(value v) {
	return;
    }

    static struct custom_operations program_ops = {
	(char*) "goto.program",
	finalize_program,
	custom_compare_default,
	custom_hash_default,
	custom_serialize_default,
	custom_deserialize_default
    };

    /** function custom operations ********************************************/
    void finalize_function(value v) {
	return;
    }

    static struct custom_operations function_ops = {
	(char*) "goto.function",
	finalize_function,
	custom_compare_default,
	custom_hash_default,
	custom_serialize_default,
	custom_deserialize_default
    };

    /** tuple & list operations ***********************************************/
    static inline value tuple(value a, value b) {
	CAMLparam2(a, b);
	CAMLlocal1(tuple);

	tuple = caml_alloc(2, 0);

	Store_field(tuple, 0, a);
	Store_field(tuple, 1, b);

	CAMLreturn(tuple);
    }

    static inline value append(value hd, value tl) {
	CAMLparam2(hd, tl);
	CAMLreturn(tuple(hd, tl));
    }

    /***************************************************************************
     * Wrappers
     **************************************************************************/
    value wrapper_read_binary (value filename) {
	CAMLparam1(filename);
	CAMLlocal1(r);
	r = alloc_custom(&program_ops, sizeof(program *), 0, 1);
	Program_val(r) = new std::pair<goto_functionst, contextt>();
	const std::string filestr(String_val(filename));
	ui_message_handlert msg_handler(ui_message_handlert::PLAIN, filestr);
	read_goto_binary(filestr,
			 Program_val(r)->second,
			 Program_val(r)->first,
			 msg_handler);

	namespacet ns(Program_val(r)->second);
	remove_function_pointers(ns, Program_val(r)->first);
	string_abstraction(Program_val(r)->second,
			   msg_handler,
			   Program_val(r)->first);
	goto_inline(Program_val(r)->first, ns, msg_handler);
	remove_unused_functions(Program_val(r)->first, msg_handler);
	CAMLreturn(r);
    }

    value wrapper_iter_functions (value gp) {
	CAMLparam1(gp);
	CAMLlocal2(name,fun);
	program *gf = Program_val(gp);
	value* f = caml_named_value("__iter_functions_handler");
	forall_goto_functions(f_it, gf->first) {
	    fun = alloc_custom(&function_ops, sizeof(goto_functiont *), 0, 1);
	    Function_val(fun) = &(f_it->second);
	    name = caml_copy_string(f_it->first.c_str());
	    caml_callback2(*f, name, fun);
	}
	CAMLreturn(Val_unit);
    }

    value expr_operands(exprt expr) {
	CAMLparam0();
	CAMLlocal1(operands);
	operands = Val_emptylist;
	exprt::operandst::reverse_iterator it;
	if (expr.has_operands()) {
	    for (it = expr.operands().rbegin();
		 it!=expr.operands().rend();
		 it++)
		{
		    operands = append(alloc_irep(*it), operands);
		}
	}
	CAMLreturn(operands);
    }

    value wrapper_irep_operands(value v) {
	CAMLparam1(v);
	CAMLreturn(expr_operands(*((exprt*) Irep_val(v))));
    }

    value wrapper_instr_operands(value v) {
	CAMLparam1(v);
	CAMLreturn(expr_operands((**(Instr_val(v))).code));
    }

#define INSTR_ACCESSOR(name, instr, exp)		\
    value wrapper_instr_ ## name (value v) {		\
	CAMLparam1(v);					\
	instructiont instr = **(Instr_val(v));		\
	CAMLreturn(exp);				\
    }

    INSTR_ACCESSOR(type, instr, Val_instrtype(instr.type));
    INSTR_ACCESSOR(guard, instr, alloc_irep(instr.guard));
    INSTR_ACCESSOR(location, instr, alloc_irep(instr.location));

    value wrapper_instr_successors(value funv, value instrv) {
	CAMLparam2(funv, instrv);
	CAMLlocal1(succs);
	goto_programt::const_targetst successors;
	const goto_functiont* fun = Function_val(funv);
	targett* instr = Instr_val(instrv);

	fun->body.get_successors(*instr, successors);
	succs = Val_emptylist;
	for(goto_programt::const_targetst::reverse_iterator
		t_it = successors.rbegin();
	    t_it!=successors.rend();
	    t_it++)
	    {
		succs = append(alloc_instr(*t_it), succs);
	    }
	CAMLreturn(succs);
    }

    value wrapper_print_instr (value v);

    value wrapper_iter_instr (value gf) {
	CAMLparam1(gf);
	CAMLlocal1(instr);
	const goto_functiont* fun = Function_val(gf);
	value* f = caml_named_value("__iter_instr_handler");
	forall_goto_program_instructions(i_it, fun->body) {
	    caml_callback(*f, alloc_instr(i_it));
	}
	CAMLreturn(Val_unit);
    }

#define SYMBOL_ACCESSOR(name, sym, exp)		\
    value wrapper_symbol_ ## name (value v) {	\
	CAMLparam1(v);				\
	symbolt* sym = Symbol_val(v);		\
	CAMLreturn(exp);			\
    }

    SYMBOL_ACCESSOR(static_lifetime, sym, Val_int(sym->static_lifetime))
    SYMBOL_ACCESSOR(is_extern, sym, Val_int(sym->is_extern))
    SYMBOL_ACCESSOR(base_name, sym, caml_copy_string(sym->base_name.c_str()))
    SYMBOL_ACCESSOR(type, sym, alloc_irep(sym->type));
    SYMBOL_ACCESSOR(value, sym, alloc_irep(sym->value));
    SYMBOL_ACCESSOR(location, sym, alloc_irep(sym->location));
    SYMBOL_ACCESSOR(is_lvalue, sym, Val_int(sym->lvalue));
    SYMBOL_ACCESSOR(is_type, sym, Val_int(sym->is_type));
    SYMBOL_ACCESSOR(is_macro, sym, Val_int(sym->is_macro));


    value wrapper_iter_symbol (value gf) {
	CAMLparam1(gf);
	CAMLlocal2(name, pretty_name);
	program* p = Program_val(gf);
	value* f = caml_named_value("__iter_symbol_handler");
	Forall_symbols(s_it, p->second.symbols) {
	    name = caml_copy_string(s_it->first.c_str());
	    caml_callback2(*f, name, alloc_symbol(s_it->second));
	}
	CAMLreturn(Val_unit);
    }

    value wrapper_expr_constant (value expr) {
	CAMLparam1(expr);
	CAMLlocal1(name);
	name = caml_copy_string(((exprt*) expr)->get(ID_value).c_str());
	CAMLreturn(name);
    }

    value wrapper_irep_find (value irep, value key) {
	CAMLparam2(irep, key);
	CAMLreturn(alloc_irep((Irep_val(irep))->find(String_val(key))));
    }

    value wrapper_irep_find_string (value irepv, value key) {
	CAMLparam2(irepv, key);
	CAMLlocal1(val);
	irept *irep = Irep_val(irepv);
	val = caml_copy_string(irep->get_string(String_val(key)).c_str());
	CAMLreturn(val);
    }

    value wrapper_irep_string (value irep) {
	CAMLparam1(irep);
	CAMLlocal1(id);
	id = caml_copy_string(Irep_val(irep)->id().c_str());
	CAMLreturn(id);
    }

    value wrapper_irep_arguments (value irep) {
	CAMLparam1(irep);
	CAMLlocal1(arguments);
	code_typet *type = (code_typet*) Irep_val(irep);
	code_typet::argumentst::reverse_iterator it;
	arguments = Val_emptylist;
	if (type->arguments().size() > 0) {
	    for (it = type->arguments().rbegin();
		 it != type->arguments().rend();
		 it++) {
		arguments = append(alloc_irep(*it), arguments);
	    }
	}
	CAMLreturn(arguments);
    }

    value wrapper_irep_components (value irep) {
	CAMLparam1(irep);
	CAMLlocal1(components);
	struct_union_typet *struct_rep = (struct_union_typet*) Irep_val(irep);
	struct_union_typet::componentst::reverse_iterator it;
	components = Val_emptylist;
	for (it = struct_rep->components().rbegin();
	     it != struct_rep->components().rend();
	     it++) {
	    components = append(alloc_irep(*it), components);
	}
	CAMLreturn(components);
    }

    value wrapper_print_irep (value v) {
	CAMLparam1(v);
	std::cout << *(Irep_val(v)) << std::endl;
	CAMLreturn(Val_unit);
    }

    value wrapper_print_instr (value v) {
	CAMLparam1(v);
	std::cout << "* Type: " << (**(Instr_val(v))).type << std::endl
		  << "* Guard: " << (**(Instr_val(v))).guard << std::endl
		  << "* Code:  " << (**(Instr_val(v))).code << std::endl;
	CAMLreturn(Val_unit);
    }

    value wrapper_print_symbol (value v) {
	CAMLparam1(v);
	std::cout << *Symbol_val(v) << std::endl;
	CAMLreturn(Val_unit);
    }

}
