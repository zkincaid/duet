/***************************************************
** $Id: hash.c,v 1.3 2013/01/31 18:51:06 bcx Exp $
****************************************************/
/* config.h.  Generated from config.h.in by configure.  */
/* config.h.in.  Generated from configure.ac by autoheader.  */

/* Define if building universal (internal helper macro) */
/* #undef AC_APPLE_UNIVERSAL_BUILD */

/* Define to 1 if you have the `bcopy' function. */
/* #undef HAVE_BCOPY */

/* Define to 1 if you have the `bzero' function. */
/* #undef HAVE_BZERO */

/* Define to 1 if you have the <ctype.h> header file. */
#define HAVE_CTYPE_H 1

/* Define to 1 if you have the <errno.h> header file. */
#define HAVE_ERRNO_H 1

/* Define to 1 if you have the <fcntl.h> header file. */
#define HAVE_FCNTL_H 1

/* Define to 1 if you have the <inttypes.h> header file. */
#define HAVE_INTTYPES_H 1

/* Define to 1 if your system has a GNU libc compatible `malloc' function, and
   to 0 otherwise. */
#define HAVE_MALLOC 1

/* Define to 1 if you have the `memcpy' function. */
#define HAVE_MEMCPY 1

/* Define to 1 if you have the <memory.h> header file. */
#define HAVE_MEMORY_H 1

/* Define to 1 if you have the `memset' function. */
#define HAVE_MEMSET 1

/* Define to 1 if you have the <netdb.h> header file. */
#define HAVE_NETDB_H 1

/* Define to 1 if you have the <poll.h> header file. */
#define HAVE_POLL_H 1

/* Define to 1 if you have the <pthread.h> header file. */
#define HAVE_PTHREAD_H 1

/* Define to 1 if your system has a GNU libc compatible `realloc' function,
   and to 0 otherwise. */
#define HAVE_REALLOC 1

/* Define to 1 if you have the <stdint.h> header file. */
#define HAVE_STDINT_H 1

/* Define to 1 if you have the <stdio.h> header file. */
#define HAVE_STDIO_H 1

/* Define to 1 if you have the <stdlib.h> header file. */
#define HAVE_STDLIB_H 1

/* Define to 1 if you have the `strcasecmp' function. */
#define HAVE_STRCASECMP 1

/* Define to 1 if you have the `strdup' function. */
#define HAVE_STRDUP 1

/* Define to 1 if you have the <strings.h> header file. */
#define HAVE_STRINGS_H 1

/* Define to 1 if you have the <string.h> header file. */
#define HAVE_STRING_H 1

/* Define to 1 if you have the <syslog.h> header file. */
#define HAVE_SYSLOG_H 1

/* Define to 1 if you have the <sys/stat.h> header file. */
#define HAVE_SYS_STAT_H 1

/* Define to 1 if you have the <sys/types.h> header file. */
#define HAVE_SYS_TYPES_H 1

/* Define to 1 if you have the <time.h> header file. */
#define HAVE_TIME_H 1

/* Define to 1 if you have the <unistd.h> header file. */
#define HAVE_UNISTD_H 1

/* Name of package */
#define PACKAGE "libhash"

/* Define to the address where bug reports for this package should be sent. */
#define PACKAGE_BUGREPORT "bcx+libhash@bcx.com"

/* Define to the full name of this package. */
#define PACKAGE_NAME "libhash"

/* Define to the full name and version of this package. */
#define PACKAGE_STRING "libhash 0.3"

/* Define to the one symbol short name of this package. */
#define PACKAGE_TARNAME "libhash"

/* Define to the home page for this package. */
#define PACKAGE_URL ""

/* Define to the version of this package. */
#define PACKAGE_VERSION "0.3"

/* The size of `char', as computed by sizeof. */
#define SIZEOF_CHAR 1

/* The size of `int', as computed by sizeof. */
#define SIZEOF_INT 4

/* The size of `long', as computed by sizeof. */
#define SIZEOF_LONG 8

/* The size of `long long', as computed by sizeof. */
#define SIZEOF_LONG_LONG 8

/* The size of `short', as computed by sizeof. */
#define SIZEOF_SHORT 2

/* The size of `size_t', as computed by sizeof. */
#define SIZEOF_SIZE_T 8

/* The size of `unsigned long long', as computed by sizeof. */
#define SIZEOF_UNSIGNED_LONG_LONG 8

/* The size of `void *', as computed by sizeof. */
#define SIZEOF_VOID_P 8

/* Define to 1 if you have the ANSI C header files. */
#define STDC_HEADERS 1

/* Define to 1 if you can safely include both <sys/time.h> and <time.h>. */
#define TIME_WITH_SYS_TIME 1

/* Define to 1 if your <sys/time.h> declares `struct tm'. */
/* #undef TM_IN_SYS_TIME */

/* Version number of package */
#define VERSION "0.3"

/* Define WORDS_BIGENDIAN to 1 if your processor stores words with the most
   significant byte first (like Motorola and SPARC, unlike Intel). */
#if defined AC_APPLE_UNIVERSAL_BUILD
# if defined __BIG_ENDIAN__
#  define WORDS_BIGENDIAN 1
# endif
#else
# ifndef WORDS_BIGENDIAN
/* #  undef WORDS_BIGENDIAN */
# endif
#endif

/* Define to empty if `const' does not conform to ANSI C. */
/* #undef const */

/* Define to rpl_malloc if the replacement function should be used. */
/* #undef malloc */

/* Define to rpl_realloc if the replacement function should be used. */
/* #undef realloc */

/* Define to `unsigned int' if <sys/types.h> does not define. */
/* #undef size_t */
# if HAVE_CTYPE_H
#       include <ctype.h>
# endif
# if HAVE_ERRNO_H
#       include <errno.h>
# endif
# if HAVE_MEMORY_H
#       include <memory.h>
# endif
# if TM_IN_SYS_TIME
#       include <sys/time.h>
# else
#       include <time.h>
# endif
# if TIME_WITH_SYS_TIME && TM_IN_SYS_TIME
#       include <time.h>
# endif
# if HAVE_STDLIB_H
#       include <stdlib.h>
# endif
# if HAVE_STRING_H
#       include <string.h>
# endif
# if HAVE_SYS_TYPES_H
#       include <sys/types.h>
# endif
# if HAVE_STDINT_H
#       include <stdint.h>
# endif
# if HAVE_UNISTD_H
#       include <unistd.h>
# endif
# if HAVE_PTHREAD_H
#       include <pthread.h>
# endif

#ifndef HASH_H
#define HASH_H 1

typedef struct entry_bucket {
	struct entry_bucket *previous;
	struct entry_bucket *next;
	char  *key;
	void  *data;
	time_t timestamp;
} HASH_BUCKET;

typedef struct {
	HASH_BUCKET   *bucket;
	pthread_mutex_t  mutex;
} HASH_SHELF;

#define	MIN_SHELVES_LG2	4
#define	MIN_SHELVES	(1 << MIN_SHELVES_LG2)

/*
 * max * sizeof internal_entry must fit into size_t.
 * assumes internal_entry is <= 32 (2^5) bytes.
 */
#define	MAX_SHELVES_LG2	(sizeof (size_t) * 8 - 1 - 5)
#define	MAX_SHELVES	((size_t)1 << MAX_SHELVES_LG2)

typedef struct {
	HASH_SHELF *	table;
	size_t		tablesize;
	void (*freefunct)(void *);
} HASH_CTX;

#define DEFAULT_HASH_TABLESIZE	(2048)

HASH_CTX *	hash_init(size_t tablesize);
HASH_CTX *	hash_shutdown(HASH_CTX *hctx);
void		hash_set_callback(HASH_CTX *hctx, void (*callback)(void *));
void *		hash_lookup(HASH_CTX *hctx, char *string, void *data, size_t datalen);
int		hash_drop(HASH_CTX *hctx, char *string);
int		hash_expire(HASH_CTX *hctx, time_t age);

#endif /* HASH_H */

/********************************************************************
** HASH_SET_CALLBACK -- Set the callback for freeing the data
**
**	Parameters:
**		ctx		-- Hash table context
**		callback	-- address of freeing function
**	Returns:
**		void		-- nothing
**	Side Effects:
**		None.
**	Notes:
**		The free function must be declared as:
**			void *funct(void *arg);
*/
void
hash_set_callback(HASH_CTX *hctx, void (*callback)(void *))
{
	if (hctx == NULL)
		return;
	hctx->freefunct = callback;
	return;
}

/********************************************************************
** HASH_STRING -- Convert a string into its hash value.
**
**	Parameters:
**		string	-- string to hash
**		limit	-- size of the hash table
**	Returns:
**		unsigned integer of hash value
**		if str == NULL hashes ""
**	Side Effects:
**		None.
**	Notes:
**		Generally for internal use only.
*/
static size_t
hash_string(char *str, size_t limit)
{
	size_t  hash;
	size_t  highorder;
	int 	c;
	char *	s;

	if (str == NULL)
		s = "";
	else
		s = str;

	/*
	 * Changed to a more modern CRC hash.
	 */
	hash = 5381;
	highorder = hash & 0xf8000000;
	do
	{
		c = (int)(*s);
		if (c == 0)
			break;
		hash = hash << 5;
		hash = hash ^ (highorder >> 27);
		hash = hash ^ c;
		highorder = hash & 0xf8000000;
		++s;
	} while (c != 0);
	return hash % limit;
}

/********************************************************************
** HASH_INIT -- Allocate and receive a context pointer
**
**	Parameters:
**		tablesize	-- size of the internal hash table
**	Returns:
**		Address of type HASH_CTX *
**		NULL on error and sets errno.
**	Side Effects:
**		Allocates memory.
**		Initializes tablesize number of mutexes
**	Notes:
**		If tablesize is zero, defaults to (2048)
**		Tablesize should be a power of two, if not, it
**		is silently adjusted to a power of two.
**	If you want a callback to free your data, call
**	hash_set_callback() immediately after this call.
*/
HASH_CTX *
hash_init(size_t tablesize)
{
	size_t i;
	unsigned int p2;
	HASH_CTX *hctx;

	hctx = malloc(sizeof(HASH_CTX));
	if (hctx == NULL) 
	{
		if (errno == 0)
			errno = ENOMEM;
		return NULL;
	}

	if (tablesize == 0)
		hctx->tablesize = DEFAULT_HASH_TABLESIZE;
	else
		hctx->tablesize = tablesize;

	hctx->freefunct = NULL;

	/* 
	 * If buckets is too small, make it min sized. 
	 */
	if (hctx->tablesize < MIN_SHELVES)
		hctx->tablesize = MIN_SHELVES;

	/* 
	 * If it's too large, cap it. 
	 */
	if (hctx->tablesize > MAX_SHELVES)
		hctx->tablesize = MAX_SHELVES;

	/* 
	 * If it's is not a power of two in size, round up. 
	 */
	if ((hctx->tablesize & (hctx->tablesize - 1)) != 0) 
	{
		for (p2 = 0; hctx->tablesize != 0; p2++)
			hctx->tablesize >>= 1;

		if (p2 <= MAX_SHELVES_LG2)
			hctx->tablesize = DEFAULT_HASH_TABLESIZE;
		else
			hctx->tablesize = 1 << p2;
	}

	hctx->table = calloc(hctx->tablesize, sizeof(HASH_SHELF));
	if (hctx->table == NULL) 
	{
		if (errno == 0)
			errno = ENOMEM;
		(void) free(hctx);
		return NULL;
	}
	for (i = 0; i < hctx->tablesize; i++)
	{
		(void) pthread_mutex_init(&(hctx->table[i].mutex), NULL);
		hctx->table[i].bucket = NULL;
	}

	return hctx;
}

/********************************************************************
** HASH_FREEBUCKET -- Free a bucket.
**
**	Parameters:
**		b	-- pointer to a bucket
**	Returns:
**		NULL always.
**		errno is non-zero on error
**	Side Effects:
**		Frees memory.
**	Notes:
**		Intended for internal use only.
**		Does not unlink b from linked list.
**		NO NOT mutex lock here.
*/
static HASH_BUCKET *
hash_freebucket(HASH_CTX *hctx, HASH_BUCKET *b)
{
	if (b == NULL)
		return NULL;
	if (b->key != NULL)
	{
		(void) free(b->key);
		b->key = NULL;
	}
	if (b->data != NULL)
	{
		if (hctx != NULL && hctx->freefunct != NULL)
		{
			(hctx->freefunct)(b->data);
			b->data = NULL;
		}
		else
		{
			(void) free(b->data);
			b->data = NULL;
		}
	}
	(void) free(b);
	b = NULL;
	return NULL;
}

/********************************************************************
** HASH_SHUTDOWN -- Give up and free a hash table.
**
**	Parameters:
**		hctx	-- A hash context from hash_init()
**	Returns:
**		NULL always.
**		errno is non-zero on error
**	Side Effects:
**		Frees memory.
**	Notes:
**		None
*/
HASH_CTX *
hash_shutdown(HASH_CTX *hctx)
{
	unsigned int i;
	HASH_BUCKET *t, *b;

	if (hctx == NULL)
	{
		errno = EINVAL;
		return NULL;
	}

	if (hctx->table == NULL || hctx->tablesize == 0)
	{
		errno = EINVAL;
		return NULL;
	}

	for (i = 0; i < hctx->tablesize; i++) 
	{
		(void) pthread_mutex_destroy(&(hctx->table[i].mutex));
		if ((hctx->table[i].bucket) == NULL)
			continue;
		
		b = hctx->table[i].bucket;
		do
		{
			t = b->next;
			b = hash_freebucket(hctx, b);
			b = t;

		} while (b != NULL);
	}
	(void) free(hctx->table);
	hctx->table = NULL;
	(void) free(hctx);
	hctx = NULL;
	errno = 0;
	return NULL;
}

/********************************************************************
** HASH_LOOKUP -- Look up a key and get its data
**
**	Parameters:
**		hctx	-- A hash context from hash_init()
**		string	-- The string to lookup
**		data	-- Data for update only (NULL for plain lookup)
**		datalen -- Size in bytes of the data blob
**	Returns:
**		Address of data on success (search or update)
**		NULL and sets non-zero errno on error
**	Side Effects:
**		Allocates memory on update.
**	Notes:
**		If data is NULL, just lookup string and return data if found.
**		If data not NULL, insert if string not found, but if found,
**			replace the old data with the new.
*/
void *
hash_lookup(HASH_CTX *hctx, char *string, void *data, size_t datalen)
{
	uint32_t hashval;
	HASH_BUCKET *b, *n;

	if (data != NULL && datalen == 0)
	{
		errno = EINVAL;
		return NULL;
	}

	if (string == NULL)
	{
		errno = EINVAL;
		return NULL;
	}

	if (hctx == NULL || hctx->table == NULL || hctx->tablesize == 0)
	{
		errno = EINVAL;
		return NULL;
	}


	hashval = hash_string(string, hctx->tablesize);

	(void) pthread_mutex_lock(&(hctx->table[hashval].mutex));
	 b = hctx->table[hashval].bucket;
	 if (b != NULL)
	 {
		do
		{
			if (b->key != NULL && strcasecmp(string, b->key) == 0)
			{
				if (data != NULL)
				{
					if (hctx->freefunct != NULL)
						(hctx->freefunct)(b->data);
					else
						(void) free(b->data);

					b->data = calloc(1, datalen);
					if (b->data == NULL)
					{
						(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
						errno = ENOMEM;
						return NULL;
					}
					memcpy(b->data, data, datalen);
					(void) time(&(b->timestamp));
				}
				(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
				errno = 0;
				return b->data;
			}
			b = b->next;
		} while (b != NULL);
	 }
	 if (data == NULL)
	 {
		(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
	 	errno = 0;
	 	return NULL;
	 }

	 /*
	  * Not found, so we inert it.
	  */
	 n = calloc(1, sizeof(HASH_BUCKET));
	 if (n == NULL)
	 {
		(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
		errno = ENOMEM;
		return NULL;
	 }
	 n->next = n->previous = NULL;
	 n->key = strdup(string);
	 if (n->key == NULL)
	 {
		(void) free(n);
		n = NULL;
		(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
		errno = ENOMEM;
		return NULL;
	 }
	 n->data = calloc(1, datalen);
	 if (n->data == NULL)
	 {
		(void) free(n->key);
		n->key = NULL;
		(void) free(n);
		n = NULL;
		(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
		errno = ENOMEM;
		return NULL;
	 }
	 memcpy(n->data, data, datalen);
	 (void) time(&(n->timestamp));

	 b = hctx->table[hashval].bucket;
	 if (b == NULL)
	 {
	 	hctx->table[hashval].bucket = n;
		(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
		errno = 0;
	 	return n->data;
	 }
	 while (b->next != NULL)
	 	b = b->next;
	 b->next = n;
	 n->previous = b;
	(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));

	errno = 0;
	return n->data;
}
 
/********************************************************************
** HASH_DROP -- Remove a key/data from the hash table
**
**	Parameters:
**		hctx	-- A hash context from hash_init()
**		string	-- The string to remove
**	Returns:
**		Zero on success
**		Returns non-zero errno on error
**	Side Effects:
**		Frees memory
**	Notes:
**		If string not in the table, returns zero anyway.
*/
int
hash_drop(HASH_CTX *hctx, char *string)
{
	uint32_t hashval;
	HASH_BUCKET *b;

	if (string == NULL)
	{
		return errno = EINVAL;
	}

	if (hctx == NULL || hctx->table == NULL || hctx->tablesize == 0)
	{
		return errno = EINVAL;
	}

	hashval = hash_string(string, hctx->tablesize);

	(void) pthread_mutex_lock(&(hctx->table[hashval].mutex));
	 b = hctx->table[hashval].bucket;
	 if (b != NULL)
	 {
		do
		{
			if (b->key != NULL && strcasecmp(string, b->key) == 0)
			{
				if (b->previous != NULL)
					b->previous->next = b->next;
				if (b->next != NULL)
					b->next->previous = b->previous;
				b = hash_freebucket(hctx, b);
				(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
				return errno = 0;
			}
			b = b->next;
		} while (b != NULL);
	 }
	(void) pthread_mutex_unlock(&(hctx->table[hashval].mutex));
	return errno = 0;
}
 
/********************************************************************
** HASH_EXPIRE -- Remove old data from the hash table
**
**	Parameters:
**		hctx	-- A hash context from hash_init()
**		age	-- Maximum age to retain
**	Returns:
**		Zero on success
**		Returns non-zero errno on error
**	Side Effects:
**		Frees memory
**	Notes:
**		The age is in seconds. All entries older than
**		age are removed from the table.
*/
int
hash_expire(HASH_CTX *hctx, time_t age)
{
	HASH_BUCKET *b, *t;
	time_t 		now;
	unsigned int		i;

	if (age == 0)
	{
		return errno = EINVAL;
	}

	if (hctx == NULL || hctx->table == NULL || hctx->tablesize == 0)
	{
		return errno = EINVAL;
	}

	(void) time(&now);
	for (i = 0; i < hctx->tablesize; i++)
	{

		(void) pthread_mutex_lock(&(hctx->table[i].mutex));
		 b = hctx->table[i].bucket;
		 if (b != NULL)
		 {
			do
			{
				t = b->next;
				if ((now - b->timestamp) > age)
				{
					if (b->previous != NULL)
						b->previous->next = b->next;
					if (b->next != NULL)
						b->next->previous = b->previous;
					if (b == hctx->table[i].bucket)
						hctx->table[i].bucket = t;
					b = hash_freebucket(hctx, b);
				}
				b = t;
			} while (b != NULL);
		 }
		(void) pthread_mutex_unlock(&(hctx->table[i].mutex));
	}
	return errno = 0;
}

void freefun(void *arg) { return; }

void foo(HASH_CTX * hctx) {
  int i = rand() % 5;
  int n;
  char str[80];
  char * data;
  time_t tm;

  while(i) {
    for(int j = 0; j < 80; j++) str[j] = rand();
    if (i == 1) {
      hash_lookup(hctx, str, NULL, 0);
    } else if (i == 2) {
      n = rand();
      data = malloc(n * sizeof(char));
      hash_lookup(hctx, str, data, n);
    } else if (i == 3) {
      hash_drop(hctx, str);
    } else {
      time(&tm);
      hash_expire(hctx, tm);
    }
    i = rand() % 5;
  }   
}

int main() {
  pthread_t t[8];
  HASH_CTX *ht = hash_init(0);
  hash_set_callback(ht, &freefun);

  for(int i = 0; i < 8; i++) {
    pthread_create(&(t[i]), NULL, &foo, (void *)ht);
  }
  
  return 0;
}
