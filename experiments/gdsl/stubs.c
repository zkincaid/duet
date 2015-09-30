int fprintf(FILE * __restrict  __stream , char const   * __restrict  __format, ...) {
    return 0;
}
int printf(char const   * __restrict  __format 
                   , ...) {
    return 0;
}
int sprintf(char *str, const char *format, ...) {
    int limit, i;
    limit = rand();
    for (i = 0; i < limit; i++) {
	*(str + limit) = rand();
    }
    return limit;
}
void free(void *x){
    // unsound!!!
}
size_t strlen(const char *str) {
    size_t len = 0;
    while (*str) {
	str++;
	len++;
    }
    return len;
}
char *strcpy(char *destination, char *source){
    while(*source) {
	*(destination++) = *(source++);
    }
    *destination = '0';
    return destination;
}

int strcmp(const char *s1, const char *s2) {
    while(*s1) {
	int diff = *(s1++) - *(s2++);
	if (diff != 0) {
	    return diff;
	}
    }
    return 0;
}

char *strcat(char *restrict destination, const char *restrict source) {
    while(*destination) {
	destination++;
    }
    while(*source) {
	*(destination++) = *(source++);
	source++;
    }
    return destination;
}

char* strdup(char* s) {
    char *buf;
    buf = malloc(strlen(s)+1);
    return strcpy(buf, s);
}

void * memcpy (void * destination, const void * source, size_t num) {
    size_t i;
    for (i = 0; i < num; i++) {
	*((char*)destination++) = *((char*)source++);
    }
    return destination;
}

#include <sys/time.h>
int gettimeofday(struct timeval *tv, struct timezone *tz) {
    if (tv) {
	tv->tv_sec = rand();
	tv->tv_usec = rand();
    }
    if (tz) {
	tz->tz_minuteswest = rand();
	tz->tz_dsttime = rand();
    }
    if (rand()) {
	return 0; // success
    } else {
	return -1; // failure
    }
}

// seed PRNG (ignored)
void srand(unsigned int seed){ }

void scanf(char *s, int *x) {
    *x = rand();
}

int atoi(const char *nptr) {
    return rand();
}
