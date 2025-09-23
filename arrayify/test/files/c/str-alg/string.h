#include <stdlib.h>
#include <stdint.h>
extern char __VERIFIER_nondet_char();
#define BLK_SIZE 1000


#undef __GNUC__
#ifdef __GNUC__
typedef __attribute__((__may_alias__)) size_t WT;
#define WS (sizeof(WT))
#endif
#define UCHAR_MAX 255
#define ALIGN (sizeof(size_t))
#define ONES ((size_t)-1/UCHAR_MAX)
#define HIGHS (ONES * (UCHAR_MAX/2+1))
#define HASZERO(x) ((x)-ONES & ~(x) & HIGHS)
#define BITOP(a,b,op) \
 ((a)[(size_t)(b)/(8*sizeof *(a))] op (size_t)1<<((size_t)(b)%(8*sizeof *(a))))
#define SS (sizeof(size_t))

void *__memrchr(const void *m, int c, size_t n)
{
	const unsigned char *s = m;
	c = (unsigned char)c;
	while (n--) if (s[n]==c) return (void *)(s+n);
	return 0;
}

void *memchr2(const void *src, int c, size_t n)
{
	const unsigned char *s = src;
	c = (unsigned char)c;
#ifdef __GNUC__
	for (; ((uintptr_t)s & ALIGN) && n && *s != c; s++, n--);
	if (n && *s != c) {
		typedef size_t __attribute__((__may_alias__)) word;
		const word *w;
		size_t k = ONES * c;
		for (w = (const void *)s; n>=SS && !HASZERO(*w^k); w++, n-=SS);
		s = (const void *)w;
	}
#endif
	for (; n && *s != c; s++, n--);
	return n ? (void *)s : 0;
}

int memcmp2(const void *vl, const void *vr, size_t n)
{
	const unsigned char *l=vl, *r=vr;
	for (; n && *l == *r; n--, l++, r++);
	return n ? *l-*r : 0;
}

void *memcpy2(void *restrict dest, const void *restrict src, size_t n)
{
	unsigned char *d = dest;
	const unsigned char *s = src;
/*
#ifdef __GNUC__

#if __BYTE_ORDER == __LITTLE_ENDIAN
#define LS >>
#define RS <<
#else
#define LS <<
#define RS >>
#endif

	typedef uint32_t __attribute__((__may_alias__)) u32;
	uint32_t w, x;

	for (; (uintptr_t)s % 4 && n; n--) *d++ = *s++;

	if ((uintptr_t)d % 4 == 0) {
		for (; n>=16; s+=16, d+=16, n-=16) {
			*(u32 *)(d+0) = *(u32 *)(s+0);
			*(u32 *)(d+4) = *(u32 *)(s+4);
			*(u32 *)(d+8) = *(u32 *)(s+8);
			*(u32 *)(d+12) = *(u32 *)(s+12);
		}
		if (n&8) {
			*(u32 *)(d+0) = *(u32 *)(s+0);
			*(u32 *)(d+4) = *(u32 *)(s+4);
			d += 8; s += 8;
		}
		if (n&4) {
			*(u32 *)(d+0) = *(u32 *)(s+0);
			d += 4; s += 4;
		}
		if (n&2) {
			*d++ = *s++; *d++ = *s++;
		}
		if (n&1) {
			*d = *s;
		}
		return dest;
	}

	if (n >= 32) switch ((uintptr_t)d % 4) {
	case 1:
		w = *(u32 *)s;
		*d++ = *s++;
		*d++ = *s++;
		*d++ = *s++;
		n -= 3;
		for (; n>=17; s+=16, d+=16, n-=16) {
			x = *(u32 *)(s+1);
			*(u32 *)(d+0) = (w LS 24) | (x RS 8);
			w = *(u32 *)(s+5);
			*(u32 *)(d+4) = (x LS 24) | (w RS 8);
			x = *(u32 *)(s+9);
			*(u32 *)(d+8) = (w LS 24) | (x RS 8);
			w = *(u32 *)(s+13);
			*(u32 *)(d+12) = (x LS 24) | (w RS 8);
		}
		break;
	case 2:
		w = *(u32 *)s;
		*d++ = *s++;
		*d++ = *s++;
		n -= 2;
		for (; n>=18; s+=16, d+=16, n-=16) {
			x = *(u32 *)(s+2);
			*(u32 *)(d+0) = (w LS 16) | (x RS 16);
			w = *(u32 *)(s+6);
			*(u32 *)(d+4) = (x LS 16) | (w RS 16);
			x = *(u32 *)(s+10);
			*(u32 *)(d+8) = (w LS 16) | (x RS 16);
			w = *(u32 *)(s+14);
			*(u32 *)(d+12) = (x LS 16) | (w RS 16);
		}
		break;
	case 3:
		w = *(u32 *)s;
		*d++ = *s++;
		n -= 1;
		for (; n>=19; s+=16, d+=16, n-=16) {
			x = *(u32 *)(s+3);
			*(u32 *)(d+0) = (w LS 8) | (x RS 24);
			w = *(u32 *)(s+7);
			*(u32 *)(d+4) = (x LS 8) | (w RS 24);
			x = *(u32 *)(s+11);
			*(u32 *)(d+8) = (w LS 8) | (x RS 24);
			w = *(u32 *)(s+15);
			*(u32 *)(d+12) = (x LS 8) | (w RS 24);
		}
		break;
	}
	if (n&16) {
		*d++ = *s++; *d++ = *s++; *d++ = *s++; *d++ = *s++;
		*d++ = *s++; *d++ = *s++; *d++ = *s++; *d++ = *s++;
		*d++ = *s++; *d++ = *s++; *d++ = *s++; *d++ = *s++;
		*d++ = *s++; *d++ = *s++; *d++ = *s++; *d++ = *s++;
	}
	if (n&8) {
		*d++ = *s++; *d++ = *s++; *d++ = *s++; *d++ = *s++;
		*d++ = *s++; *d++ = *s++; *d++ = *s++; *d++ = *s++;
	}
	if (n&4) {
		*d++ = *s++; *d++ = *s++; *d++ = *s++; *d++ = *s++;
	}
	if (n&2) {
		*d++ = *s++; *d++ = *s++;
	}
	if (n&1) {
		*d = *s;
	}
	return dest;
#endif
*/
	for (; n; n--) *d++ = *s++;
	return dest;
}


void *memmove2(void *dest, const void *src, size_t n)
{
	char *d = dest;
	const char *s = src;

	if (d==s) return d;
	if ((uintptr_t)s-(uintptr_t)d-n <= -2*n) return memcpy2(d, s, n);

	if (d<s) {
#ifdef __GNUC__
		if ((uintptr_t)s % WS == (uintptr_t)d % WS) {
			while ((uintptr_t)d % WS) {
				if (!n--) return dest;
				*d++ = *s++;
			}
			for (; n>=WS; n-=WS, d+=WS, s+=WS) *(WT *)d = *(WT *)s;
		}
#endif
		for (; n; n--) *d++ = *s++;
	} else {
#ifdef __GNUC__
		if ((uintptr_t)s % WS == (uintptr_t)d % WS) {
			while ((uintptr_t)(d+n) % WS) {
				if (!n--) return dest;
				d[n] = s[n];
			}
			while (n>=WS) n-=WS, *(WT *)(d+n) = *(WT *)(s+n);
		}
#endif
		while (n) n--, d[n] = s[n];
	}

	return dest;
}


void *memset2(void *dest, int c, size_t n)
{
	unsigned char *s = dest;
	size_t k;

	/* Fill head and tail with minimal branching. Each
	 * conditional ensures that all the subsequently used
	 * offsets are well-defined and in the dest region. */

	if (!n) return dest;
	s[0] = c;
	s[n-1] = c;
	if (n <= 2) return dest;
	s[1] = c;
	s[2] = c;
	s[n-2] = c;
	s[n-3] = c;
	if (n <= 6) return dest;
	s[3] = c;
	s[n-4] = c;
	if (n <= 8) return dest;

	/* Advance pointer to align it at a 4-byte boundary,
	 * and truncate n to a multiple of 4. The previous code
	 * already took care of any head/tail that get cut off
	 * by the alignment. */

	k = -(uintptr_t)s & 3;
	s += k;
	n -= k;
	n &= -4;

#ifdef __GNUC__
	typedef uint32_t __attribute__((__may_alias__)) u32;
	typedef uint64_t __attribute__((__may_alias__)) u64;

	u32 c32 = ((u32)-1)/255 * (unsigned char)c;

	/* In preparation to copy 32 bytes at a time, aligned on
	 * an 8-byte bounary, fill head/tail up to 28 bytes each.
	 * As in the initial byte-based head/tail fill, each
	 * conditional below ensures that the subsequent offsets
	 * are valid (e.g. !(n<=24) implies n>=28). */

	*(u32 *)(s+0) = c32;
	*(u32 *)(s+n-4) = c32;
	if (n <= 8) return dest;
	*(u32 *)(s+4) = c32;
	*(u32 *)(s+8) = c32;
	*(u32 *)(s+n-12) = c32;
	*(u32 *)(s+n-8) = c32;
	if (n <= 24) return dest;
	*(u32 *)(s+12) = c32;
	*(u32 *)(s+16) = c32;
	*(u32 *)(s+20) = c32;
	*(u32 *)(s+24) = c32;
	*(u32 *)(s+n-28) = c32;
	*(u32 *)(s+n-24) = c32;
	*(u32 *)(s+n-20) = c32;
	*(u32 *)(s+n-16) = c32;

	/* Align to a multiple of 8 so we can fill 64 bits at a time,
	 * and avoid writing the same bytes twice as much as is
	 * practical without introducing additional branching. */

	k = 24 + ((uintptr_t)s & 4);
	s += k;
	n -= k;

	/* If this loop is reached, 28 tail bytes have already been
	 * filled, so any remainder when n drops below 32 can be
	 * safely ignored. */

	u64 c64 = c32 | ((u64)c32 << 32);
	for (; n >= 32; n-=32, s+=32) {
		*(u64 *)(s+0) = c64;
		*(u64 *)(s+8) = c64;
		*(u64 *)(s+16) = c64;
		*(u64 *)(s+24) = c64;
	}
#else
	/* Pure C fallback with no aliasing violations. */
	for (; n; n--, s++) *s = c;
#endif

	return dest;
}


size_t strlen(const char *s)
{
	const char *a = s;
#ifdef __GNUC__
	typedef size_t __attribute__((__may_alias__)) word;
	const word *w;
	for (; (uintptr_t)s % ALIGN; s++) if (!*s) return s-a;
	for (w = (const void *)s; !HASZERO(*w); w++);
	s = (const void *)w;
#endif
	for (; *s; s++);
	return s-a;
}

char *__stpcpy(char *restrict d, const char *restrict s)
{
#ifdef __GNUC__
	typedef size_t __attribute__((__may_alias__)) word;
	word *wd;
	const word *ws;
	if ((uintptr_t)s % ALIGN == (uintptr_t)d % ALIGN) {
		for (; (uintptr_t)s % ALIGN; s++, d++)
			if (!(*d=*s)) return d;
		wd=(void *)d; ws=(const void *)s;
		for (; !HASZERO(*ws); *wd++ = *ws++);
		d=(void *)wd; s=(const void *)ws;
	}
#endif
	for (; (*d=*s); s++, d++);

	return d;
}

char *strcpy(char *restrict dest, const char *restrict src)
{
	__stpcpy(dest, src);
	return dest;
}


char *strcat(char *restrict dest, const char *restrict src)
{
	strcpy(dest + strlen(dest), src);
	return dest;
}

char *strncat(char *restrict d, const char *restrict s, size_t n)
{
	char *a = d;
	d += strlen(d);
	while (n && *s) n--, *d++ = *s++;
	*d++ = 0;
	return a;
}

char *__strchrnul(const char *s, int c)
{
	c = (unsigned char)c;
	if (!c) return (char *)s + strlen(s);

#ifdef __GNUC__
	typedef size_t __attribute__((__may_alias__)) word;
	const word *w;
	for (; (uintptr_t)s % ALIGN; s++)
		if (!*s || *(unsigned char *)s == c) return (char *)s;
	size_t k = ONES * c;
	for (w = (void *)s; !HASZERO(*w) && !HASZERO(*w^k); w++);
	s = (void *)w;
#endif
	for (; *s && *(unsigned char *)s != c; s++);
	return (char *)s;
}

char *strchr(const char *s, int c)
{
	char *r = __strchrnul(s, c);
	return *(unsigned char *)r == (unsigned char)c ? r : 0;
}

char *strrchr(const char *s, int c)
{
	return __memrchr(s, c, strlen(s) + 1);
}

int strcmp(const char *l, const char *r)
{
	for (; *l==*r && *l; l++, r++);
	return *(unsigned char *)l - *(unsigned char *)r;
}

int strncmp(const char *_l, const char *_r, size_t n)
{
	const unsigned char *l=(void *)_l, *r=(void *)_r;
	if (!n--) return 0;
	for (; *l && *r && n && *l == *r ; l++, r++, n--);
	return *l - *r;
}

char *__stpncpy(char *restrict d, const char *restrict s, size_t n)
{
#ifdef __GNUC__
	typedef size_t __attribute__((__may_alias__)) word;
	word *wd;
	const word *ws;
	if (((uintptr_t)s & ALIGN) == ((uintptr_t)d & ALIGN)) {
		for (; ((uintptr_t)s & ALIGN) && n && (*d=*s); n--, s++, d++);
		if (!n || !*s) goto tail;
		wd=(void *)d; ws=(const void *)s;
		for (; n>=sizeof(size_t) && !HASZERO(*ws);
		       n-=sizeof(size_t), ws++, wd++) *wd = *ws;
		d=(void *)wd; s=(const void *)ws;
	}
#endif
	for (; n && (*d=*s); n--, s++, d++);
tail:
	memset2(d, 0, n);
	return d;
}

char *strncpy(char *restrict d, const char *restrict s, size_t n)
{
	__stpncpy(d, s, n);
	return d;
}

size_t strcspn(const char *s, const char *c)
{
	const char *a = s;
	size_t byteset[32/sizeof(size_t)];

	if (!c[0] || !c[1]) return __strchrnul(s, *c)-a;

	memset2(byteset, 0, sizeof byteset);
	for (; *c && BITOP(byteset, *(unsigned char *)c, |=); c++);
	for (; *s && !BITOP(byteset, *(unsigned char *)s, &); s++);
	return s-a;
}


size_t strspn(const char *s, const char *c)
{
	const char *a = s;
	size_t byteset[32/sizeof(size_t)] = { 0 };

	if (!c[0]) return 0;
	if (!c[1]) {
		for (; *s == *c; s++);
		return s-a;
	}

	for (; *c && BITOP(byteset, *(unsigned char *)c, |=); c++);
	for (; *s && BITOP(byteset, *(unsigned char *)s, &); s++);
	return s-a;
}

char *strtok(char *restrict s, const char *restrict sep)
{
	static char *p;
	if (!s && !(s = p)) return NULL;
	s += strspn(s, sep);
	if (!*s) return p = 0;
	p = s + strcspn(s, sep);
	if (*p) *p++ = 0;
	else p = 0;
	return s;
}

static char *twobyte_strstr(const unsigned char *h, const unsigned char *n)
{
	uint16_t nw = n[0]<<8 | n[1], hw = h[0]<<8 | h[1];
	for (h++; *h && hw != nw; hw = hw<<8 | *++h);
	return *h ? (char *)h-1 : 0;
}

static char *threebyte_strstr(const unsigned char *h, const unsigned char *n)
{
	uint32_t nw = (uint32_t)n[0]<<24 | n[1]<<16 | n[2]<<8;
	uint32_t hw = (uint32_t)h[0]<<24 | h[1]<<16 | h[2]<<8;
	for (h+=2; *h && hw != nw; hw = (hw|*++h)<<8);
	return *h ? (char *)h-2 : 0;
}

static char *fourbyte_strstr(const unsigned char *h, const unsigned char *n)
{
	uint32_t nw = (uint32_t)n[0]<<24 | n[1]<<16 | n[2]<<8 | n[3];
	uint32_t hw = (uint32_t)h[0]<<24 | h[1]<<16 | h[2]<<8 | h[3];
	for (h+=3; *h && hw != nw; hw = hw<<8 | *++h);
	return *h ? (char *)h-3 : 0;
}

#define MAX(a,b) ((a)>(b)?(a):(b))
#define MIN(a,b) ((a)<(b)?(a):(b))

#define BITOP(a,b,op) \
 ((a)[(size_t)(b)/(8*sizeof *(a))] op (size_t)1<<((size_t)(b)%(8*sizeof *(a))))

static char *twoway_strstr(const unsigned char *h, const unsigned char *n)
{
	const unsigned char *z;
	size_t l, ip, jp, k, p, ms, p0, mem, mem0;
	size_t byteset[32 / sizeof(size_t)] = { 0 };
	size_t shift[256];

	/* Computing length of needle and fill shift table */
	for (l=0; n[l] && h[l]; l++)
		BITOP(byteset, n[l], |=), shift[n[l]] = l+1;
	if (n[l]) return 0; /* hit the end of h */

	/* Compute maximal suffix */
	ip = -1; jp = 0; k = p = 1;
	while (jp+k<l) {
		if (n[ip+k] == n[jp+k]) {
			if (k == p) {
				jp += p;
				k = 1;
			} else k++;
		} else if (n[ip+k] > n[jp+k]) {
			jp += k;
			k = 1;
			p = jp - ip;
		} else {
			ip = jp++;
			k = p = 1;
		}
	}
	ms = ip;
	p0 = p;

	/* And with the opposite comparison */
	ip = -1; jp = 0; k = p = 1;
	while (jp+k<l) {
		if (n[ip+k] == n[jp+k]) {
			if (k == p) {
				jp += p;
				k = 1;
			} else k++;
		} else if (n[ip+k] < n[jp+k]) {
			jp += k;
			k = 1;
			p = jp - ip;
		} else {
			ip = jp++;
			k = p = 1;
		}
	}
	if (ip+1 > ms+1) ms = ip;
	else p = p0;

	/* Periodic needle? */
	if (memcmp2(n, n+p, ms+1)) {
		mem0 = 0;
		p = MAX(ms, l-ms-1) + 1;
	} else mem0 = l-p;
	mem = 0;

	/* Initialize incremental end-of-haystack pointer */
	z = h;

	/* Search loop */
	for (;;) {
		/* Update incremental end-of-haystack pointer */
		if (z-h < l) {
			/* Fast estimate for MAX(l,63) */
			size_t grow = l | 63;
			const unsigned char *z2 = memchr2(z, 0, grow);
			if (z2) {
				z = z2;
				if (z-h < l) return 0;
			} else z += grow;
		}

		/* Check last byte first; advance by shift on mismatch */
		if (BITOP(byteset, h[l-1], &)) {
			k = l-shift[h[l-1]];
			if (k) {
				if (k < mem) k = mem;
				h += k;
				mem = 0;
				continue;
			}
		} else {
			h += l;
			mem = 0;
			continue;
		}

		/* Compare right half */
		for (k=MAX(ms+1,mem); n[k] && n[k] == h[k]; k++);
		if (n[k]) {
			h += k-ms;
			mem = 0;
			continue;
		}
		/* Compare left half */
		for (k=ms+1; k>mem && n[k-1] == h[k-1]; k--);
		if (k <= mem) return (char *)h;
		h += p;
		mem = mem0;
	}
}

char *strstr(const char *h, const char *n)
{
	/* Return immediately on empty needle */
	if (!n[0]) return (char *)h;

	/* Use faster algorithms for short needles */
	h = strchr(h, *n);
	if (!h || !n[1]) return (char *)h;
	if (!h[1]) return 0;
	if (!n[2]) return twobyte_strstr((void *)h, (void *)n);
	if (!h[2]) return 0;
	if (!n[3]) return threebyte_strstr((void *)h, (void *)n);
	if (!h[3]) return 0;
	if (!n[4]) return fourbyte_strstr((void *)h, (void *)n);

	return twoway_strstr((void *)h, (void *)n);
}

char *strpbrk(const char *s, const char *b)
{
	s += strcspn(s, b);
	return *s ? (char *)s : 0;
}

void init(int size, char *dest) {
  for (int i = 0 ; i < size - 1; i++ ) {
    char c = __VERIFIER_nondet_char();
    dest[i] = c;
  }
  dest[size - 1] = '\0';
}

