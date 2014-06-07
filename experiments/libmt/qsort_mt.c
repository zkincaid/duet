/*-
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
 * Multithread implementation Copyright (c) 2006, 2007 Diomidis Spinellis.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#if defined(LIBC_SCCS) && !defined(lint)
static char sccsid[] = "@(#)qsort.c	8.1 (Berkeley) 6/4/93";
#endif /* LIBC_SCCS and not lint */
#include <sys/cdefs.h>
#ifdef __FBSDID
__FBSDID("$FreeBSD: src/lib/libc/stdlib/qsort.c,v 1.12 2002/09/10 02:04:49 wollman Exp $");
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <pthread.h>

#include <sys/types.h>
#include <errno.h>
#include <stdio.h>

#include <unistd.h>
/* config.h.  Generated from config.h.in by configure.  */
/* config.h.in.  Generated from configure.in by autoheader.  */

/* Define to 1 if you have the <dlfcn.h> header file. */
#define HAVE_DLFCN_H 1

/* Define to 1 if you have the `getrusage' function. */
#define HAVE_GETRUSAGE 1

/* Define to 1 if you have the <inttypes.h> header file. */
#define HAVE_INTTYPES_H 1

/* Define to 1 if you have the `pthread' library (-lpthread). */
#define HAVE_LIBPTHREAD 1

/* Define to 1 if your system has a GNU libc compatible `malloc' function, and
   to 0 otherwise. */
#define HAVE_MALLOC 1

/* Define to 1 if you have the `memcmp' function. */
#define HAVE_MEMCMP 1

/* Define to 1 if you have the <memory.h> header file. */
#define HAVE_MEMORY_H 1

/* Define to 1 if you have the `mergesort' function. */
/* #undef HAVE_MERGESORT */

/* Define to 1 if you have the `pthread_create' function. */
/* #undef HAVE_PTHREAD_CREATE */

/* Define to 1 if you have the <pthread.h> header file. */
#define HAVE_PTHREAD_H 1

/* Define to 1 if you have the `pthread_join' function. */
/* #undef HAVE_PTHREAD_JOIN */

/* Define to 1 if you have the <stdint.h> header file. */
#define HAVE_STDINT_H 1

/* Define to 1 if you have the <stdlib.h> header file. */
#define HAVE_STDLIB_H 1

/* Define to 1 if you have the <strings.h> header file. */
#define HAVE_STRINGS_H 1

/* Define to 1 if you have the <string.h> header file. */
#define HAVE_STRING_H 1

/* Define to 1 if you have the `strtol' function. */
#define HAVE_STRTOL 1

/* Define to 1 if you have the `sysconf' function. */
#define HAVE_SYSCONF 1

/* Define to 1 if you have the `sysctl' function. */
#define HAVE_SYSCTL 1

/* Define to 1 if you have the <sys/stat.h> header file. */
#define HAVE_SYS_STAT_H 1

/* Define to 1 if you have the <sys/types.h> header file. */
#define HAVE_SYS_TYPES_H 1

/* Define to 1 if you have the <unistd.h> header file. */
#define HAVE_UNISTD_H 1

/* Define to the sub-directory in which libtool stores uninstalled libraries.
   */
#define LT_OBJDIR ".libs/"

/* Name of package */
#define PACKAGE "libmt"

/* Define to the address where bug reports for this package should be sent. */
#define PACKAGE_BUGREPORT "mail@mweissmann.de"

/* Define to the full name of this package. */
#define PACKAGE_NAME "libmt"

/* Define to the full name and version of this package. */
#define PACKAGE_STRING "libmt 0.1"

/* Define to the one symbol short name of this package. */
#define PACKAGE_TARNAME "libmt"

/* Define to the version of this package. */
#define PACKAGE_VERSION "0.1"

/* Define to 1 if you have the ANSI C header files. */
#define STDC_HEADERS 1

/* Version number of package */
#define VERSION "0.1"

/* Define to empty if `const' does not conform to ANSI C. */
/* #undef const */

/* Define to `__inline__' or `__inline' if that's what the C compiler
   calls it, or to nothing if 'inline' is not supported under any name.  */
#ifndef __cplusplus
/* #undef inline */
#endif

/* Define to rpl_malloc if the replacement function should be used. */
/* #undef malloc */

/* Define to `unsigned int' if <sys/types.h> does not define. */
/* #undef size_t */

/* multi-threaded quick sort */
void
qsort_mt(void *a, size_t n, size_t es, int (*compar)(const void *, const void *));

/* multi-threaded quick sort with explicit bounds */
void
qsort_mts(void *a, size_t n, size_t es, int (*compar)(const void *, const void *), int maxthreads, size_t forkelem);

int hw_cores() {
	int ncpus = 1;

#if defined HAVE_SYSCTL && defined CTL_HW && defined HW_NCPU
	int mib[2];
	size_t len;

	mib[0] = CTL_HW;
	mib[1] = HW_NCPU;
	len = sizeof(ncpus);
	sysctl(mib, 2, &ncpus, &len, NULL, 0);
#elif HAVE_SYSCONF
	ncpus = sysconf(_SC_NPROCESSORS_ONLN);
#else
#error Cannot determine number of cores dynamically
#endif

	return (ncpus > 0) ? ncpus : 1;
}

/*
 * Defining the following macro will cause all
 * pthreads API invocation to be checked, against
 * invocation errors (e.g. trying to lock an uninitialized
 * mutex.  Other errors (e.g. unavailable resources)
 * are always checked and acted upon.
 */
#define DEBUG_API 0

/*
 * Defining the followin macro will print on stderr the results
 * of various sort phases.
 */
/* #define DEBUG_SORT 1 */

/*
 * Defining the following macro will produce logging
 * information on the algorithm's progress
 */
/* #define DEBUG_LOG 1 */

#ifdef DEBUG_API
#define verify(x) do {				\
	int e;					\
	if ((e = x) != 0) {			\
		fprintf(stderr, "%s(%d) %s: %s\n",\
		    __FILE__, __LINE__,		\
		    #x, strerror(e)); 		\
		exit(1);			\
	}					\
} while(0)
#else /* !DEBUG_API */
#define verify(x) (x)
#endif

#ifdef DEBUG_LOG
#define DLOG(...) fprintf(stderr, __VA_ARGS__)
#else
#define DLOG(...)
#endif

#ifdef I_AM_QSORT_R
typedef int		 cmp_t(void *, const void *, const void *);
#else
typedef int		 cmp_t(const void *, const void *);
#endif
static inline char	*med3(char *, char *, char *, cmp_t *, void *);
static inline void	 swapfunc(char *, char *, int, int);

#define min(a, b)	(a) < (b) ? a : b

/*
 * Qsort routine from Bentley & McIlroy's "Engineering a Sort Function".
 */
#define swapcode(TYPE, parmi, parmj, n) { 		\
	long i = (n) / sizeof (TYPE); 			\
	TYPE *pi = (TYPE *) (parmi); 		\
	TYPE *pj = (TYPE *) (parmj); 		\
	do { 						\
		TYPE	t = *pi;		\
		*pi++ = *pj;				\
		*pj++ = t;				\
        } while (--i > 0);				\
}


static inline void
swapfunc(a, b, n, swaptype)
	char *a, *b;
	int n, swaptype;
{
	if(swaptype <= 1)
		swapcode(long, a, b, n)
	else
		swapcode(char, a, b, n)
}

#define swap(a, b)					\
	if (swaptype == 0) {				\
		long t = *(long *)(a);			\
		*(long *)(a) = *(long *)(b);		\
		*(long *)(b) = t;			\
	} else						\
		swapfunc(a, b, es, swaptype)

#define vecswap(a, b, n) 	if ((n) > 0) swapfunc(a, b, n, swaptype)

#ifdef I_AM_QSORT_R
#define	CMP(t, x, y) (cmp((t), (x), (y)))
#else
#define	CMP(t, x, y) (cmp((x), (y)))
#endif

static inline char *
med3(char *a, char *b, char *c, cmp_t *cmp, void *thunk
#ifndef I_AM_QSORT_R
//__unused
#endif
)
{
	return CMP(thunk, a, b) < 0 ?
	       (CMP(thunk, b, c) < 0 ? b : (CMP(thunk, a, c) < 0 ? c : a ))
              :(CMP(thunk, b, c) > 0 ? b : (CMP(thunk, a, c) < 0 ? a : c ));
}

/*
 * We use some elaborate condition variables and signalling
 * to ensure a bound of the number of active threads at
 * 2 * maxthreads and the size of the thread data structure
 * to maxthreads.
 */

/* Condition of starting a new thread. */
enum thread_state {
	ts_idle,		/* Idle, waiting for instructions. */
	ts_work,		/* Has work to do. */
	ts_term			/* Asked to terminate. */
};

/* Variant part passed to qsort invocations. */
struct qsort {
	enum thread_state st;	/* For coordinating work. */
	struct common *common;	/* Common shared elements. */
	void *a;		/* Array base. */
	size_t n;		/* Number of elements. */
	pthread_t id;		/* Thread id. */
	pthread_mutex_t mtx_st;	/* For signalling state change. */
	pthread_cond_t cond_st;	/* For signalling state change. */
};

/* Invariant common part, shared across invocations. */
struct common {
	int swaptype;		/* Code to use for swapping */
	size_t es;		/* Element size. */
	void *thunk;		/* Thunk for qsort_r */
	cmp_t *cmp;		/* Comparison function */
	int nthreads;		/* Total number of pool threads. */
	int idlethreads;	/* Number of idle threads in pool. */
	int forkelem;		/* Minimum number of elements for a new thread. */
	struct qsort *pool;	/* Fixed pool of threads. */
	pthread_mutex_t mtx_al;	/* For allocating threads in the pool. */
};

static void *qsort_thread(void *p);
static struct qsort *qsort_launch(struct qsort *qs);

void
qsort_mt(void *a, size_t n, size_t es, cmp_t *cmp) {
	qsort_mts(a, n, es, cmp, hw_cores(), 10);
}

/* The multithreaded qsort public interface */
void
qsort_mts(void *a, size_t n, size_t es, cmp_t *cmp, int maxthreads, size_t forkelem)
{
	struct qsort *qs;
	struct common c;
	int i, islot;
	bool bailout = true;

	if (n < forkelem)
		goto f1;
	errno = 0;

	/* XXX temporarily disabled for stress and performance testing.
	if (maxthreads == 1)
		goto f1;
	*/
	/* Try to initialize the resources we need. */
	if (pthread_mutex_init(&c.mtx_al, NULL) != 0)
		goto f1;
	if ((c.pool = (struct qsort *)calloc(maxthreads, sizeof(struct qsort))) ==NULL)
		goto f2;
	for (islot = 0; islot < maxthreads; islot++) {
		qs = &c.pool[islot];
		if (pthread_mutex_init(&qs->mtx_st, NULL) != 0)
			goto f3;
		if (pthread_cond_init(&qs->cond_st, NULL) != 0) {
			verify(pthread_mutex_destroy(&qs->mtx_st));
			goto f3;
		}
		qs->st = ts_idle;
		qs->common = &c;
		if (pthread_create(&qs->id, NULL, qsort_thread, qs) != 0) {
			verify(pthread_mutex_destroy(&qs->mtx_st));
			verify(pthread_cond_destroy(&qs->cond_st));
			goto f3;
		}
	}

	/* All systems go. */
	bailout = false;

	/* Initialize common elements. */
	c.swaptype = ((char *)a - (char *)0) % sizeof(long) || \
		es % sizeof(long) ? 2 : es == sizeof(long)? 0 : 1;
	c.es = es;
	c.cmp = cmp;
	c.forkelem = forkelem;
	c.idlethreads = c.nthreads = maxthreads;

	/* Hand out the first work batch. */
	qs = &c.pool[0];
	verify(pthread_mutex_lock(&qs->mtx_st));
	qs->a = a;
	qs->n = n;
	qs->st = ts_work;
	c.idlethreads--;
	verify(pthread_cond_signal(&qs->cond_st));
	verify(pthread_mutex_unlock(&qs->mtx_st));

	/* 
	 * Wait for all threads to finish, and
	 * free acquired resources.
	 */
f3:	for (i = 0; i < islot; i++) {
		qs = &c.pool[i];
		if (bailout) {
			verify(pthread_mutex_lock(&qs->mtx_st));
			qs->st = ts_term;
			verify(pthread_cond_signal(&qs->cond_st));
			verify(pthread_mutex_unlock(&qs->mtx_st));
		}
		verify(pthread_join(qs->id, NULL));
		verify(pthread_mutex_destroy(&qs->mtx_st));
		verify(pthread_cond_destroy(&qs->cond_st));
	}
	free(c.pool);
f2:	verify(pthread_mutex_destroy(&c.mtx_al));
	if (bailout) {
		DLOG("Resource initialization failed; bailing out.\n");
		/* XXX should include a syslog call here */
		fprintf(stderr, "Resource initialization failed; bailing out.\n");
f1:		qsort(a, n, es, cmp);
	}
}

#define thunk NULL

/*
 * Allocate an idle thread from the pool, lock its
 * mutex, change its state to work, decrease the number
 * of idle threads, and return a
 * pointer to its data area.
 * Return NULL, if no thread is available.
 */
static struct qsort *
allocate_thread(struct common *c)
{
	int i;

	verify(pthread_mutex_lock(&c->mtx_al));
	for (i = 0; i < c->nthreads; i++)
		if (c->pool[i].st == ts_idle) {
			c->idlethreads--;
			c->pool[i].st = ts_work;
			verify(pthread_mutex_lock(&c->pool[i].mtx_st));
			verify(pthread_mutex_unlock(&c->mtx_al));
			return (&c->pool[i]);
		}
	verify(pthread_mutex_unlock(&c->mtx_al));
	return (NULL);
}

/* Thread-callable quicksort. */
static void
qsort_algo(struct qsort *qs)
{
	char *pa, *pb, *pc, *pd, *pl, *pm, *pn;
	int d, r, swaptype, swap_cnt;
	void *a;			/* Array of elements. */
	size_t n, es;			/* Number of elements; size. */
	cmp_t *cmp;
	int nl, nr;
	struct common *c;
	struct qsort *qs2;
	pthread_t id;

	/* Initialize qsort arguments. */
	id = qs->id;
	c = qs->common;
	es = c->es;
	cmp = c->cmp;
	swaptype = c->swaptype;
	a = qs->a;
	n = qs->n;
top:
	DLOG("%10x n=%-10d Sort starting.\n", id, n);
#ifdef DEBUG_SORT
	for (i = 0; i < n; i++)
		fprintf(stderr, "%d ", ((int*)a)[i]);
	putc('\n', stderr);
#endif

	/* From here on qsort(3) business as usual. */
	swap_cnt = 0;
	if (n < 7) {
		for (pm = (char *)a + es; pm < (char *)a + n * es; pm += es)
			for (pl = pm;
			     pl > (char *)a && CMP(thunk, pl - es, pl) > 0;
			     pl -= es)
				swap(pl, pl - es);
		return;
	}
	pm = (char *)a + (n / 2) * es;
	if (n > 7) {
		pl = a;
		pn = (char *)a + (n - 1) * es;
		if (n > 40) {
			d = (n / 8) * es;
			pl = med3(pl, pl + d, pl + 2 * d, cmp, thunk);
			pm = med3(pm - d, pm, pm + d, cmp, thunk);
			pn = med3(pn - 2 * d, pn - d, pn, cmp, thunk);
		}
		pm = med3(pl, pm, pn, cmp, thunk);
	}
	swap(a, pm);
	pa = pb = (char *)a + es;

	pc = pd = (char *)a + (n - 1) * es;
	for (;;) {
		while (pb <= pc && (r = CMP(thunk, pb, a)) <= 0) {
			if (r == 0) {
				swap_cnt = 1;
				swap(pa, pb);
				pa += es;
			}
			pb += es;
		}
		while (pb <= pc && (r = CMP(thunk, pc, a)) >= 0) {
			if (r == 0) {
				swap_cnt = 1;
				swap(pc, pd);
				pd -= es;
			}
			pc -= es;
		}
		if (pb > pc)
			break;
		swap(pb, pc);
		swap_cnt = 1;
		pb += es;
		pc -= es;
	}
	if (swap_cnt == 0) {  /* Switch to insertion sort */
		for (pm = (char *)a + es; pm < (char *)a + n * es; pm += es)
			for (pl = pm;
			     pl > (char *)a && CMP(thunk, pl - es, pl) > 0;
			     pl -= es)
				swap(pl, pl - es);
		return;
	}

	pn = (char *)a + n * es;
	r = min(pa - (char *)a, pb - pa);
	vecswap(a, pb - r, r);
	r = min(pd - pc, pn - pd - es);
	vecswap(pb, pn - r, r);

	nl = (pb - pa) / es;
	nr = (pd - pc) / es;
	DLOG("%10x n=%-10d Partitioning finished ln=%d rn=%d.\n", id, n, nl, nr);

	/* Now try to launch subthreads. */
	if (nl > c->forkelem && nr > c->forkelem &&
	    (qs2 = allocate_thread(c)) != NULL) {
		DLOG("%10x n=%-10d Left farmed out to %x.\n", id, n, qs2->id);
		qs2->a = a;
		qs2->n = nl;
		verify(pthread_cond_signal(&qs2->cond_st));
		verify(pthread_mutex_unlock(&qs2->mtx_st));
	} else if (nl > 0) {
		DLOG("%10x n=%-10d Left will be done in-house.\n", id, n);
		qs->a = a;
		qs->n = nl;
		qsort_algo(qs);
	}
	if (nr > 0) {
		DLOG("%10x n=%-10d Right will be done in-house.\n", id, n);
		a = pn - nr * es;
		n = nr;
		goto top;
	}
}

/* Thread-callable quicksort. */
static void *
qsort_thread(void *p)
{
	struct qsort *qs, *qs2;
	int i;
	struct common *c;
	pthread_t id;

	qs = p;
	id = qs->id;
	c = qs->common;
again:
	/* Wait for work to be allocated. */
	DLOG("%10x n=%-10d Thread waiting for work.\n", id, 0);
	verify(pthread_mutex_lock(&qs->mtx_st));
	while (qs->st == ts_idle)
		verify(pthread_cond_wait(&qs->cond_st, &qs->mtx_st));
	verify(pthread_mutex_unlock(&qs->mtx_st));
	if (qs->st == ts_term) {
		DLOG("%10x n=%-10d Thread signalled to exit.\n", id, 0);
		return NULL;
	}
	assert(qs->st == ts_work);

	qsort_algo(qs);

	verify(pthread_mutex_lock(&c->mtx_al));
	qs->st = ts_idle;
	c->idlethreads++;
	DLOG("%10x n=%-10d Finished idlethreads=%d.\n", id, 0, c->idlethreads);
	if (c->idlethreads == c->nthreads) {
		DLOG("%10x n=%-10d All threads idle, signalling shutdown.\n", id, 0);
		for (i = 0; i < c->nthreads; i++) {
			qs2 = &c->pool[i];
			if (qs2 == qs)
				continue;
			verify(pthread_mutex_lock(&qs2->mtx_st));
			qs2->st = ts_term;
			verify(pthread_cond_signal(&qs2->cond_st));
			verify(pthread_mutex_unlock(&qs2->mtx_st));
		}
		DLOG("%10x n=%-10d Shutdown signalling complete.\n", id, 0);
		verify(pthread_mutex_unlock(&c->mtx_al));
		return NULL;
	}
	verify(pthread_mutex_unlock(&c->mtx_al));
	goto again;
}

int compare(const void * a, const void * b) {
  return *((int *)a) < *((int *)b);
}

int main() {
  int n;
  int * array;

  do {
    n = rand();
    array = malloc(n * sizeof(int));
    qsort_mt((void *)array, n, sizeof(int), &compare);
  } while (rand());

  return 0;
}
