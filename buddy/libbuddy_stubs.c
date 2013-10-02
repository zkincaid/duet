/**************************************************************************/
/*  Copyright (C) 2008 Akihiko Tozawa and Masami Hagiya.                  */
/*  Copyright (C) 2009 2010 Pietro Abate <pietro.abate@pps.jussieu.fr     */
/*                                                                        */
/*  This library is free software: you can redistribute it and/or modify  */
/*  it under the terms of the GNU Lesser General Public License as        */
/*  published by the Free Software Foundation, either version 3 of the    */
/*  License, or (at your option) any later version.  A special linking    */
/*  exception to the GNU Lesser General Public License applies to this    */
/*  library, see the COPYING file for more information.                   */
/**************************************************************************/

#include <stdio.h>
#include <string.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>

#include "bdd.h"
#include "fdd.h"

/* Snippet taken from byterun/io.h of OCaml 3.11 */

#ifndef IO_BUFFER_SIZE
#define IO_BUFFER_SIZE 4096
#endif

#include <sys/types.h>
#include <unistd.h>
typedef off_t file_offset;

struct channel {
  int fd;                       /* Unix file descriptor */
  file_offset offset;           /* Absolute position of fd in the file */
  char * end;                   /* Physical end of the buffer */
  char * curr;                  /* Current position in the buffer */
  char * max;                   /* Logical end of the buffer (for input) */
  void * mutex;                 /* Placeholder for mutex (for systhreads) */
  struct channel * next, * prev;/* Double chaining of channels (flush_all) */
  int revealed;                 /* For Cash only */
  int old_revealed;             /* For Cash only */
  int refcount;                 /* For flush_all and for Cash */
  int flags;                    /* Bitfield */
  char buff[IO_BUFFER_SIZE];    /* The buffer itself */
};

#define Channel(v) (*((struct channel **) (Data_custom_val(v))))

static inline value tuple( value a, value b) {
  CAMLparam2( a, b );
  CAMLlocal1( tuple );

  tuple = caml_alloc(2, 0);

  Store_field( tuple, 0, a );
  Store_field( tuple, 1, b );

  CAMLreturn(tuple);
}

static inline value append( value hd, value tl ) {
  CAMLparam2( hd , tl );
  CAMLreturn(tuple( hd, tl ));
}

static inline int length (value l) {
  int len = 0;
  while (l != Val_emptylist) { len++ ; l = Field(l, 1); }
  return len;
}

#define BDD_val(v) (*((BDD*)Data_custom_val(v)))
#define BDDPAIR_val(v) (*((bddPair**)Data_custom_val(v)))

/* global variables (initialized by wrapper_bdd_init) */

struct custom_operations bddops; /* custom GC-enabled type */
struct custom_operations bddpairops; /* custom GC-enabled type */

/* number of bdd node allocation needed to trigger ocaml GC */

int wrapper_ocamlgc_max = 20000;

/* type bdd: linking buddy reference counters with Ocaml GC */

void _makebdd(value* vptr, BDD x) {
  int used = bdd_nodecount(x);
  bdd_addref(x);
  *vptr = alloc_custom(&bddops, sizeof (BDD), used, wrapper_ocamlgc_max);
  BDD_val(*vptr) = x;
}

void _deletebdd(value v) {
  BDD x = BDD_val(v);
  bdd_delref(x);
}

static int _comparebdd(value v1, value v2) {
  BDD p1 = BDD_val(v1);
  BDD p2 = BDD_val(v2);
  if(p1 == p2) return 0;
  if(p1 < p2) return -1;
  if(p1 > p2) return 1;
}

static long _hashbdd(value v) {
  return (long) BDD_val(v);
}

/* type bddpair: the use of custom_val here is not so important */

void _deletebddpair(value v) {
  bddPair* x = BDDPAIR_val(v);
  bdd_freepair(x);
}

CAMLprim void wrapper_bdd_init(value v1, value v2) {
  int nodesize = Int_val(v1);
  int cachesize = Int_val(v2);
  bdd_init(nodesize, cachesize);

  bddops.identifier = NULL;
  bddops.finalize = _deletebdd;
  bddops.compare = _comparebdd;
  bddops.hash = _hashbdd;
  bddops.serialize = NULL;
  bddops.deserialize = NULL;

  bddpairops.identifier = NULL;
  bddpairops.finalize = _deletebddpair;
  bddpairops.compare = NULL;
  bddpairops.hash = NULL;
  bddpairops.serialize = NULL;
  bddpairops.deserialize = NULL;
}

/* converts a Caml channel to a C FILE* stream */
static FILE * stream_of_channel(value chan, const char * mode) {
  int des;
  FILE * res ;
  struct channel *c_chan = Channel(chan) ;
  if(c_chan==NULL)
    return NULL;
  des = dup(c_chan->fd) ;
  res = fdopen(des, mode) ;
  if (des < 0 || res == NULL) {
    caml_failwith("failed to duplicate caml channel");
  }
  return res ;
}

/* wrappers */

CAMLprim value wrapper_bdd_compare(value v1, value v2) {
  CAMLparam2(v1,v2);
  CAMLreturn(Val_int(_comparebdd(v1,v2)));
}

CAMLprim value wrapper_bdd_done() {
  CAMLparam0();
  bdd_done();
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_isrunning() {
  CAMLparam0();
  CAMLlocal1(r);
  r = bdd_isrunning();
  CAMLreturn(Val_bool(r));
}

CAMLprim value wrapper_bdd_setvarnum(value num) {
  CAMLparam1(num);
  if (bdd_isrunning()) {
    bdd_setvarnum(Int_val(num));
  } else {
    caml_failwith("Buddy not initialized");
  };
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_varnum() {
  CAMLparam0();
  CAMLreturn(Val_int(bdd_varnum()));
}

CAMLprim value wrapper_bdd_newpair() {
  CAMLparam0(); 
  CAMLlocal1(r);
  bddPair* shifter;
  r = alloc_custom(&bddpairops, sizeof (bddPair*), 1, 1);
  shifter = bdd_newpair();
  BDDPAIR_val(r) = shifter;
  CAMLreturn(r);
}

CAMLprim value wrapper_bdd_fprinttable(value out, value bdd) {
  CAMLparam2(out, bdd);
  BDD x = BDD_val(bdd);
  FILE* f = stream_of_channel(out,"w");
  bdd_fprinttable(f, x);
  fflush(f);
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_fprintset(value out, value bdd) {
  CAMLparam2(out, bdd);
  BDD x = BDD_val(bdd);
  FILE* f = stream_of_channel(out,"w");
  bdd_fprintset(f, x);
  fflush(f);
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_fprintdot(value out, value bdd) {
  CAMLparam2(out, bdd);
  BDD x = BDD_val(bdd);
  FILE* f = stream_of_channel(out,"w");
  bdd_fprintdot(f, x);
  fflush(f);
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_fprintorder(value out) {
  CAMLparam1(out);
  FILE* f = stream_of_channel(out,"w");
  bdd_fprintorder(f);
  fflush(f);
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_save(value out, value bdd) {
  CAMLparam2(out, bdd);
  BDD x = BDD_val(bdd);
  FILE* f = stream_of_channel(out,"w");
  if (bdd_save(f, x) != 0) {
    caml_raise_constant(*caml_named_value("buddy_exn_IOError"));
  }
  fflush(f);
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_load(value in) {
  CAMLparam1(in);
  CAMLlocal1(r);
  BDD x;
  if (bdd_load(stream_of_channel(in,"r"), &x) != 0) {
    caml_raise_constant(*caml_named_value("buddy_exn_IOError"));
  }
  _makebdd(&r, x);
  CAMLreturn(r);
}

CAMLprim value wrapper_bdd_setvarorder(value neworder) {
  CAMLparam1(neworder);
  int h, i;
  int n[bdd_varnum()];
  int len = length(neworder);
  if (len != bdd_varnum()) {
    caml_raise_constant(*caml_named_value("buddy_exn_InvalidOrder"));
  } else {
    for (i = bdd_varnum() - 1; i >= 0; i--) { n[i] = 0; }
    i = 0;
    while (neworder != Val_emptylist) {
      h = Int_val(Field(neworder, 0));
      neworder = Field(neworder, 1);
      n[i++]=h;
//      i=i+1;
    }
    bdd_setvarorder(n);
  }
  CAMLreturn(Val_unit);
}

CAMLprim value wrapper_bdd_getvarorder() {
  CAMLparam0();
  CAMLlocal1(varorder);
  int i;
  varorder = Val_emptylist;
  for (i = bdd_varnum() - 1; i >= 0; i--) {
      varorder = append(Val_int(bdd_level2var(i)), varorder);
  }
  CAMLreturn(varorder);
}


CAMLprim value wrapper_bdd_bigapply(value clause, value op) {
  CAMLparam2(clause,op);
  CAMLlocal1(r);
  BDD x;
  if (clause == Val_emptylist) {
    caml_raise_constant(*caml_named_value("buddy_exn_EmptyList"));
  } else {
    BDD bdd = BDD_val(Field(clause, 0));
    clause = Field(clause, 1);
    while (clause != Val_emptylist) {
      x = BDD_val(Field(clause, 0));
      bdd = bdd_addref(bdd_apply(x,bdd,Int_val(op)));
      clause = Field(clause, 1);
    }
    _makebdd(&r, bdd);
  }
  CAMLreturn(r);
}

CAMLprim value wrapper_bdd_makeset(value varlist) {
  CAMLparam1(varlist);
  CAMLlocal1(r);
  BDD bdd;
  if (varlist == Val_emptylist) {
    caml_raise_constant(*caml_named_value("buddy_exn_EmptyList"));
  } else {
    int varnum = length(varlist);
    int varset[varnum];
    int i = 0;
    while (varlist != Val_emptylist) {
      varset[i++] = Int_val(Field(varlist, 0));
      varlist = Field(varlist, 1);
    }
    bdd = bdd_makeset (varset, varnum);
    _makebdd(&r, bdd);
  }
  CAMLreturn(r);
}

CAMLprim value wrapper_fdd_vars(value dval) {
    CAMLparam1( dval );
    CAMLlocal1( vars );
    int d = Int_val(dval);
    int *d_vars = fdd_vars(d);
    int d_size = fdd_varnum(d);
    
    vars = caml_alloc(d_size, 0);
    size_t i;
    for (i = 0; i < d_size; i++) {
        Store_field( vars, i, Val_int(d_vars[i]));
    }
    CAMLreturn(vars);
}

CAMLprim value wrapper_bdd_allsat(value r) {
  CAMLparam1(r);
  BDD bdd = BDD_val(r);
  value* f = caml_named_value("__allsat_handler");
  void handler(char* varset, int size) {
    CAMLlocal2(tl,v);
    int i = 0;
    tl = Val_emptylist;
    //printf("size : %d\n", size);
    for (i = 0 ; i < size; i++) {
      //printf("%d : %d\n", i, varset[i]);
      // variants in ocaml range from 0 to n-1 !!!
      switch (varset[i]) {
        case 0 : v = Val_int(0); break; // False
        case 1 : v = Val_int(1); break; // True
        case -1 : v = Val_int(2); break; // Unknown
        default : caml_failwith("Unknown variable value"); break;
      }
      if (varset[i] != -1) {
        tl = append(tuple(Val_int(i),v),tl);
      }
    }
    caml_callback(*f,tl);
    CAMLreturn0;
  }
  bdd_allsat(bdd,*handler);
  CAMLreturn(Val_unit);
}

typedef struct __DOM_LIST {
    int dom;
    struct __DOM_LIST *next;
} *dom_list;

dom_list g_domains = 0;

void free_domains() {
    dom_list c;
    while (g_domains) {
	c = g_domains;
	g_domains = g_domains->next;
	free(c);
    }
}
void append_domain(int d) {
    dom_list c = malloc(sizeof(struct __DOM_LIST));
    c->dom = d;
    c->next = g_domains;
    g_domains = c;
}

CAMLprim value wrapper_fdd_allsat(value r, value domains) {
    CAMLparam2(r, domains);
    BDD bdd = BDD_val(r);
    value* f = caml_named_value("__fdd_allsat_handler");
    while (domains != Val_emptylist) {
	append_domain(Int_val(Field(domains,0)));
	domains = Field(domains, 1);
    }
    void handler(char* varset, int size) {
	CAMLlocal3(dvals,vals,v);
	dom_list doms;
	doms = g_domains;
	dvals = Val_emptylist;
	while (doms) {
	    int i;
	    int d = doms->dom;
	    int *d_vars = fdd_vars(d);
	    vals = Val_emptylist;
	    for (i = fdd_varnum(d) - 1; i >= 0; i--) {
		switch (varset[d_vars[i]]) {
		case 0 : v = Val_int(0); break; // False
		case 1 : v = Val_int(1); break; // True
		case -1 : v = Val_int(2); break; // Unknown
		default : caml_failwith("Unknown variable value"); break;
		}
		vals = append(v,vals);
	    }
	    dvals = append(vals, dvals);
	    doms = doms->next;
	}
	caml_callback(*f,dvals);
	CAMLreturn0;
    }
    bdd_allsat(bdd,*handler);
    free_domains();
    CAMLreturn(Val_unit);
}

/* 
 * creating a set representing bdd
 * (this is here to demonstrate callback)
 */

CAMLprim value wrapper_bdd_createset(value f) {
  CAMLparam1(f); 
  CAMLlocal1(r);
  int l,v;
  BDD d,e;
  d = bdd_true ();
  for (l = bdd_varnum() - 1; l >= 0; l--) 
    {
      v = bdd_level2var(l);
      if (Bool_val(callback(f, Val_int(v)))) 
        {
          /* bdd_ithvar is always reference-counted */
          e = bdd_and(bdd_ithvar(v), d); 
          bdd_delref(d);
          bdd_addref(e);
          d = e;
        }
    }
  _makebdd(&r, d);
  CAMLreturn(r);
}

/* macro definitions */

#define FUN_ARG_bdd(x, v) \
  BDD x = BDD_val(v);

#define FUN_ARG_bddpair(x, v) \
  bddPair* x = BDDPAIR_val(v);

#define FUN_ARG_int(x, v) \
  int x = Int_val(v);

#define FUN_RET_int(eval) \
  CAMLreturn(Val_int(eval));

#define FUN_RET_unit(eval) \
  eval; \
  CAMLreturn0;

#define FUN_RET_bdd(eval) \
  CAMLlocal1(r); /* &r is GC-root */ \
  _makebdd(&r, eval); \
  CAMLreturn(r);

#define FUN0(name, ret_type) \
CAMLprim value wrapper_##name() \
{  \
  CAMLparam0(); \
  FUN_RET_##ret_type(name()); \
}

/* same as above but returns void to avoid a compiler warning */
#define FUN00(name, ret_type) \
void wrapper_##name() \
{  \
  CAMLparam0(); \
  FUN_RET_##ret_type(name()); \
}

#define FUN1(name, arg0_type, ret_type) \
CAMLprim value wrapper_##name(value v0) \
{  \
  CAMLparam1(v0); \
  FUN_ARG_##arg0_type(x, v0); \
  FUN_RET_##ret_type(name(x)); \
}

#define FUN11(name, arg0_type, ret_type) \
void wrapper_##name(value v0) \
{  \
  CAMLparam1(v0); \
  FUN_ARG_##arg0_type(x, v0); \
  FUN_RET_##ret_type(name(x)); \
}

#define FUN2(name, arg0_type, arg1_type, ret_type)  \
CAMLprim value wrapper_##name(value v0, value v1) \
{ \
  CAMLparam2(v0, v1);  \
  FUN_ARG_##arg0_type(x, v0); \
  FUN_ARG_##arg1_type(y, v1); \
  FUN_RET_##ret_type(name(x, y)); \
}

#define FUN3(name, arg0_type, arg1_type, arg2_type, ret_type) \
CAMLprim value wrapper_##name(value v0, value v1, value v2) \
{ \
  CAMLparam3(v0, v1, v2); \
  FUN_ARG_##arg0_type(x, v0); \
  FUN_ARG_##arg1_type(y, v1); \
  FUN_ARG_##arg2_type(z, v2); \
  FUN_RET_##ret_type(name(x, y, z)); \
}

#define FUN4(name, arg0_type, arg1_type, arg2_type, arg3_type, ret_type) \
  CAMLprim value wrapper_##name(value v0, value v1, value v2, value v3) \
{ \
  CAMLparam4(v0, v1, v2, v3); \
  FUN_ARG_##arg0_type(x, v0); \
  FUN_ARG_##arg1_type(y, v1); \
  FUN_ARG_##arg2_type(z, v2); \
  FUN_ARG_##arg3_type(w, v3); \
  FUN_RET_##ret_type(name(x, y, z, w)); \
}



/* wrapped primitives */

FUN0(bdd_true, bdd)
FUN0(bdd_false, bdd)
FUN1(bdd_ithvar, int, bdd)
FUN1(bdd_nithvar, int, bdd)
FUN1(bdd_not, bdd, bdd)
FUN2(bdd_and, bdd, bdd, bdd)
FUN2(bdd_or, bdd, bdd, bdd)
FUN2(bdd_xor, bdd, bdd, bdd)
FUN2(bdd_imp, bdd, bdd, bdd)
FUN2(bdd_biimp, bdd, bdd, bdd)
FUN3(bdd_ite, bdd, bdd, bdd, bdd)
FUN4(bdd_appex, bdd, bdd, int, bdd, bdd)
FUN4(bdd_appall, bdd, bdd, int, bdd, bdd)
FUN3(bdd_apply, bdd, bdd, int, bdd)
FUN1(bdd_satone, bdd, bdd)
FUN3(bdd_satoneset, bdd, bdd, bdd, bdd)
FUN2(bdd_restrict, bdd, bdd, bdd)
FUN2(bdd_simplify, bdd, bdd, bdd)
FUN1(bdd_var, bdd, int)
FUN1(bdd_high, bdd, bdd)
FUN1(bdd_low, bdd, bdd)
FUN1(bdd_support, bdd, bdd)
FUN1(bdd_nodecount, bdd, int)
FUN1(bdd_satcount, bdd, int)
FUN1(bdd_satcountln, bdd, int)
FUN3(bdd_setpair, bddpair, int, int, int)
FUN2(bdd_replace, bdd, bddpair, bdd)
FUN3(bdd_compose, bdd, bdd, bdd, bdd)

FUN2(bdd_addvarblock, bdd, int, int)
FUN3(bdd_intaddvarblock, int, int, int, int)
FUN00(bdd_varblockall, unit)
FUN11(bdd_reorder, int, unit)
FUN1(bdd_autoreorder, int, int)
FUN00(bdd_enable_reorder, unit)
FUN00(bdd_disable_reorder, unit)
FUN1(bdd_reorder_verbose, int, int)
FUN1(bdd_level2var, int, int)
FUN1(bdd_var2level, int, int)

FUN1(bdd_setcacheratio, int, int)
FUN1(bdd_setmaxincrease, int, int)
FUN1(bdd_setminfreenodes, int, int)
//FUN1(bdd_setallocnum, int, int)
//FUN1(bdd_setincreasefactor, int, int)

FUN2(bdd_exist, bdd, bdd, bdd)
FUN2(bdd_forall, bdd, bdd, bdd)

/* fdd stuff */
FUN2(fdd_overlapdomain, int, int, int)
FUN0(fdd_clearall, unit)
FUN0(fdd_domainnum, int)
FUN1(fdd_domainsize, int, int)
FUN1(fdd_varnum, int, int)
FUN2(fdd_ithvar, int, int, bdd)
FUN1(fdd_ithset, int, bdd)
FUN1(fdd_domain, int, bdd)
FUN2(fdd_equals, int, int, bdd)
FUN3(fdd_intaddvarblock, int, int, int, int)
FUN3(fdd_setpair, bddpair, int, int, int)
FUN1(fdd_printset, bdd, unit)

value wrapper_fdd_extdomain(value vsize) {
    CAMLparam1(vsize);
    int size = Int_val(vsize);
    CAMLreturn(Val_int(fdd_extdomain(&size, 1)));
}

value wrapper_fdd_replace(value bdd, value vi, value vj) {
    CAMLparam3(bdd, vi, vj);
    bddPair* table;
    BDD result;
    int i,j;

    i = Int_val(vi);
    j = Int_val(vj);
    table = bdd_newpair();
    bdd_setpairs(table, fdd_vars(i), fdd_vars(j), fdd_varnum(i));
    result = bdd_replace(BDD_val(bdd), table);
    bdd_freepair(table);
    FUN_RET_bdd(result);
}
