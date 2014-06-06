/*_
 * Copyright (c) 2006 - 2009, Markus W. Weissmann <mail@mweissmann.de>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of OpenDarwin nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * $Id: mergesort_mt.c 1 2009-02-27 20:19:56Z mwwe $
 *
 */

#include <errno.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

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
int hw_cores();
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

struct _sorter {
	void *base;
	void *tmp;
	int nel;
	size_t width;
	int (*compar)(const void *, const void *);
	int threads;
};

typedef struct _sorter sorter;

static inline void two_sort(
		void *base,
		void *tmp,
		size_t width,
		int (*compar)(const void *, const void *)
		) {
	if (compar(base, base+width) > 0) {
		memcpy(tmp, base, width);
		memcpy(base, base+width, width);
		memcpy(base+width, tmp, width);
	}
}

static inline void join_sets(
		void *base, void *a, void *b, void *tmp,
		size_t a_nel, size_t b_nel, size_t nel, size_t width,
		int (*compar)(const void *, const void *)
		) {
	size_t c;
	for (c = 0; c < (nel*width); c += width) {
		if (a_nel == 0) { // subset a is empty
			memcpy(tmp+c, b, b_nel*width);
			break;
		} else if (b_nel == 0) {  // subset b is empty
			memcpy(tmp+c, a, a_nel*width);
			break;
		} else if (compar(a,b) <= 0) {  // take member from subset a
			memcpy(tmp+c, a, width);
			a += width;
			a_nel--;
		} else {    // take member from subset b
			memcpy(tmp+c, b, width);
			b += width;
			b_nel--;
		}
	}
	memcpy(base, tmp, width*nel);
}

void
serial_mergesort(
		void *base,
		void *tmp,
		int nel,
		size_t width,
		int (*compar)(const void *, const void *)
		) {
	void *a, *b;
	int a_nel, b_nel;

	a = base;
	a_nel = (nel+1)/2;  // bigger half of array if array-width is uneven
	b = base+(a_nel)*width;
	b_nel = nel/2;      // smaller half of array if array-width is uneven

	if (a_nel == 2) {
		two_sort(a, tmp, width, compar);
	} else if (a_nel > 2) {	// no sorting necessary if width == 1
		serial_mergesort(a, tmp, a_nel, width, compar);
	}
	if (b_nel == 2) {
		two_sort(b, tmp, width, compar);
	} else if (b_nel > 1) {
		serial_mergesort(b, tmp+(a_nel)*width, b_nel, width, compar);
	}

	join_sets(base, a, b, tmp, a_nel, b_nel, nel, width, compar);
}

void *
thread_mergesort(void *arg) {
	pthread_t tid;
	sorter *in;
	void *a, *b, *tmp;
	int a_nel, b_nel;
	size_t width, nel;

	in = (sorter*)arg;
	width = in->width;
	nel = in->nel;
	tmp = in->tmp;

	if (nel == 2) {
		two_sort(in->base, tmp, width, in->compar);
		return NULL;
	}

	/* stop if there are no threads left OR if width of array is at most 3 */
	if (in->threads < 2 || nel == 3) {
		/* let's just sort this in serial */
//		#ifdef HAVE_MERGESORT
//		mergesort(in->base, tmp, nel, width, in->compar);
//		#else
		serial_mergesort(in->base, tmp, nel, width, in->compar);
//		#endif
		return NULL;
	} else {
		/* divide & conquer */
		a = in->base;	// 1st array begins at original array boundary
		a_nel = (nel+1)/2;  // bigger half of array if array-width is uneven
		b = in->base+(a_nel*width);	// 2nd array starts at mid of original one
		b_nel = nel/2;      // smaller half of array if array-width is uneven

		if (b_nel > 1) {	// prepare thread only if sorting is necessary
			int rc;
			sorter s;
			s.base = b;
			s.nel = b_nel;
			s.width = width;
			s.compar = in->compar;
			s.tmp = tmp+(a_nel*width);
			s.threads = (in->threads)/2;
			rc = pthread_create(&tid, NULL, thread_mergesort, &s);
			if (EAGAIN == rc) { // ouf of ressources
//				#ifdef HAVE_MERGESORT
//				mergesort(in->base, tmp, nel, width, in->compar);
//				#else
				serial_mergesort(in->base, tmp, nel, width, in->compar);
//				#endif
			} else {
				in->threads = (in->threads + 1)/2;
				in->nel = a_nel;
				thread_mergesort(in);

				pthread_join(tid, NULL);
			}
		} else if (a_nel == 2) {
			two_sort(in->base, tmp, width, in->compar);
		}

		join_sets(in->base, a, b, tmp, a_nel, b_nel, nel, width, in->compar);
	}
	return NULL;
}

int
mergesort_mts(void *base, size_t nel, size_t width, int (*compar)(const void *, const void *), int max_threads) {
	sorter s;
	if (1 >= nel) { /* lists with 0 or 1 elemens are sorted by definition */
		return 0;
	}
	if (0 == width) { /* width of 0 makes no sense */
		errno = EDOM;
		return 1;
	}
	if (0 >= max_threads) { /* cannot sort without at least ONE thread (the calling one) */
		errno = EDOM;
		return 2;
	}
	s.base = base;
	s.nel = nel;
	s.width = width;
	s.compar = compar;
	s.threads = max_threads;
	s.tmp = malloc(nel*width);
	if (NULL == s.tmp) {
		errno = ENOMEM;
		return 3;
	}
	thread_mergesort(&s);
	return 0;
}

int
mergesort_mt(void *base, size_t nel, size_t width, int (*compar)(const void *, const void *)) {
	return mergesort_mts(base, nel, width, compar, 2*hw_cores());
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
    mergesort_mt((void *)array, n, sizeof(int), &compare);
  } while (rand());

  return 0;
}
