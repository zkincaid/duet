/*
 *  aget  usr
 */
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include <time.h>
#include <fcntl.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <sys/socket.h>

#include <netinet/in.h>

#include <arpa/inet.h>

#include <signal.h>
#include <pthread.h>


/****************************************************************************
 *
 *  Data.h
 *
 ****************************************************************************/

#ifndef DATA_H
#define DATA_H

#include <pthread.h>
#include <netinet/in.h>


/****************************************************************************
 *
 *  Defs.h
 *
 ****************************************************************************/

#ifndef DEFS_H
#define DEFS_H


enum
{
  GETREQSIZ = 256,
  GETRECVSIZ = 512,
  HEADREQSIZ = 512,
  MAXURLSIZ = 1024,
  MAXHOSTSIZ = 1024,
  MAXIPSIZ = 16,
  MAXBUFSIZ = 512,
  MAXTHREADS = 25,
  HTTPPORT = 80,
  UNKNOWNREQ = 2,
  FTPREQ = 21,
  PROTO_HTTP = 0xFF,
  PROTO_FTP = 0x00,
  STAT_OK = 0xFF,		/* Download completed successfully      */
  STAT_INT = 0x0F,		/* ^C caught, download interrupted      */
  STAT_ERR = 0x00		/* Download finished with error         */
};


#define	PROGVERSION  "EnderUNIX Aget v0.4"
#define	HEADREQ  "HEAD %s HTTP/1.1\r\nHost: %s\r\nUser-Agent: %s\r\n\r\n"
#define	GETREQ  "GET %s HTTP/1.1\r\nHost: %s\r\nUser-Agent: %s\r\nRange: bytes=%ld-\r\nConnection: close\r\n\r\n"

#endif


typedef struct request
{
  char host[MAXHOSTSIZ];	/* Remote host  */
  char url[MAXURLSIZ];		/* URL          */
  char file[MAXBUFSIZ];		/* file name    */
  char lfile[MAXBUFSIZ];	/* if local file name is specified      */
  char ip[MAXIPSIZ];		/* Remote IP    */
  char username[MAXBUFSIZ];
  char password[MAXBUFSIZ];
  int port;
  int clength;			/* Content-length       */
  unsigned char proto;		/* Protocol             */
} request;

typedef struct thread_data
{
  struct sockaddr_in sin;
  char getstr[GETREQSIZ];
  long soffset;			/* Start offset         */
  long foffset;			/* Finish offset        */
  long offset;			/* Current Offset       */
  long clength;			/* Content Length       */
  int fd;
  pthread_t tid;		/* Thread ID            */
  unsigned char status;		/* thread exit status   */
} thread_data;

#endif

/****************************************************************************
 *
 *  Head.h
 *
 ****************************************************************************/


void http_head_req (struct request *);

/****************************************************************************
 *
 *  Resume.h
 *
 ****************************************************************************/


typedef struct hist_data
{
  struct request req;
  int nthreads;
  int bwritten;
  struct thread_data wthread[MAXTHREADS];
} hist_data;

void save_log ();
int read_log (struct hist_data *);


/****************************************************************************
 *
 *  Aget.h
 *
 ****************************************************************************/

void get (struct request *);
void resume_get (struct hist_data *);

/****************************************************************************
 *
 *  Misc.h
 *
 ****************************************************************************/

#define	LOGSIZ	1024

int calc_offset (int, int, int);
int numofthreads (int);
void parse_url (char *, struct request *);
void usage ();
void revstr (char *);		/* Reverse String                               */
void Log (char *, ...);		/* Log                                          */
void updateProgressBar (float, float);
void handleHttpRetcode (char *);

time_t t_start, t_finish;


/****************************************************************************
 *
 *  Download.h
 *
 ****************************************************************************/


void *http_get (void *);


/****************************************************************************
 *
 *  Signal.h
 *
 ****************************************************************************/

sigset_t signal_set;

void *signal_waiter (void *arg);
void sigint_handler (void);
void sigalrm_handler (void);


char *fullurl;

int nthreads;
int fsuggested = 0;

struct request *req;		/* Download jobs                */
pthread_t hthread;		/* Helper thread for signals    */
struct thread_data *wthread;	/* Worker Threads               */

extern int errno;


extern struct thread_data *wthread;
extern struct request *req;
extern int fsuggested, nthreads;
extern int bwritten;
extern pthread_t hthread;

int errno;


void get(struct request *req)
{
  int i, ret, fd, diff_sec, nok = 0;
  long soffset, foffset;
  char *fmt;

  if (req->proto == PROTO_HTTP)
    http_head_req (req);

  /* According to the content-length, get the
   * suggested number of threads to open.
   * if the user insists on his value, let it be that way,
   * use the user's value.
   */
  ret = numofthreads (req->clength);

  if (fsuggested == 0)
    {
      if (ret == 0)
	nthreads = 1;
      else
	nthreads = ret;
    }

  wthread = (struct thread_data *) malloc (nthreads * sizeof (struct thread_data));

  Log ("Downloading %s (%d bytes) from site %s(%s:%d). Number of Threads: %d",
       req->url, req->clength, req->host, req->ip, req->port, nthreads);

  if (strlen (req->lfile) != 0)
    {
      if ((fd = open (req->lfile, O_CREAT | O_RDWR, S_IRWXU)) == -1)
	{
	  fprintf (stderr, "get: cannot open file %s for writing: %s\n",
		   req->lfile, strerror (errno));
	  exit (1);
	}

    }
  else
    {
      if ((fd = open (req->file, O_CREAT | O_RDWR, S_IRWXU)) == -1)
	{
	  fprintf (stderr, "get: cannot open file %s for writing: %s\n",
		   req->lfile, strerror (errno));
	  exit (1);
	}
    }

  if ((lseek (fd, req->clength - 1, SEEK_SET)) == -1)
    {
      fprintf (stderr, "get: couldn't lseek:  %s\n", strerror (errno));
      exit (1);
    }

  if ((write (fd, "0", 1)) == -1)
    {
      fprintf (stderr, "get: couldn't allocate space for download file: %s\n",
	       strerror (errno));
      exit (1);
    }

  /* Get the starting time, prepare GET format string, and start the threads */
  fmt = (char *) malloc ((GETREQSIZ - 2) * sizeof (char));
  memset(fmt, 0, ((GETREQSIZ - 2) * sizeof (char)));

  time (&t_start);
  for (i = 0; i < nthreads; i++)
    {
      soffset = calc_offset (req->clength, i, nthreads);
      foffset = calc_offset (req->clength, i + 1, nthreads);
      wthread[i].soffset = soffset;
      wthread[i].foffset = (i == nthreads - 1 ? req->clength : foffset);
      wthread[i].sin.sin_family = AF_INET;
      wthread[i].sin.sin_addr.s_addr = inet_addr (req->ip);
      wthread[i].sin.sin_port = htons (req->port);
      wthread[i].fd = dup (fd);
      wthread[i].clength = req->clength;
      snprintf (fmt, GETREQSIZ, GETREQ, req->url, req->host, PROGVERSION,
		soffset);
      strncpy (wthread[i].getstr, fmt, GETREQSIZ);
      pthread_create (&(wthread[i].tid), NULL, http_get, &(wthread[i]));
    }
  free (fmt);


  /* Wait for all of the threads to finish... 
   * 
   * TODO: If a thread fails, restart that!
   */
  for (i = 0; i < nthreads; i++)
    {
      pthread_join (wthread[i].tid, NULL);
      if (wthread[i].status == STAT_OK)
	nok++;
    }

/*   if (nok == nthreads) */
/*     pthread_cancel (hthread); */
/*   else */
/*     pthread_join (hthread, NULL); */

  /* Get the finish time, derive some stats       */
  time (&t_finish);
  if ((diff_sec = t_finish - t_start) == 0)
    diff_sec = 1;		/* Avoid division by zero       */

  Log ("Download completed, job completed in %d seconds. (%d Kb/sec)",
       diff_sec, (req->clength / diff_sec) / 1024);
  Log ("Shutting down...");
  close (fd);
}


void
resume_get (struct hist_data *h)
{
  int i, fd, diff_sec, nok = 0;
  char *fmt;

  nthreads = h->nthreads;

  fmt = (char *) malloc ((GETREQSIZ - 2) * sizeof (char));
  memset(fmt, 0, GETREQSIZ - 2);

  wthread =
    (struct thread_data *) malloc (nthreads * sizeof (struct thread_data));
  memcpy (req, &h->req, sizeof (struct request));
  memcpy (wthread, h->wthread, sizeof (struct thread_data) * nthreads);

  Log
    ("Resuming download %s (%d bytes) from site %s(%s:%d). Number of Threads: %d",
     req->url, req->clength, req->host, req->ip, req->port, nthreads);

  if (strlen (req->lfile) != 0)
    {
      if ((fd = open (req->lfile, O_RDWR, S_IRWXU)) == -1)
	{
	  fprintf (stderr, "get: cannot open file %s for writing: %s\n",
		   req->lfile, strerror (errno));
	  exit (1);
	}

    }
  else
    {
      if ((fd = open (req->file, O_RDWR, S_IRWXU)) == -1)
	{
	  fprintf (stderr, "get: cannot open file %s for writing: %s\n",
		   req->lfile, strerror (errno));
	  exit (1);
	}
    }

  time (&t_start);


#ifdef DEBUG
  for (i = 0; i < nthreads; i++)
    printf ("Start: %ld, Finish: %ld, Offset: %ld, Diff: %ld\n",
	    wthread[i].soffset,
	    wthread[i].foffset,
	    wthread[i].offset, wthread[i].offset - wthread[i].soffset);
#endif

  for (i = 0; i < nthreads; i++)
    {
      wthread[i].soffset = wthread[i].offset;
      wthread[i].fd = dup (fd);
      snprintf (fmt, GETREQSIZ, GETREQ, req->url, req->host, PROGVERSION,
		wthread[i].offset);
      strncpy (wthread[i].getstr, fmt, GETREQSIZ);
      pthread_create (&(wthread[i].tid), NULL, http_get, &(wthread[i]));
    }

  for (i = 0; i < nthreads; i++)
    pthread_join (wthread[i].tid, NULL);

  for (i = 0; i < nthreads; i++)
    {
      pthread_join (wthread[i].tid, NULL);
      if (wthread[i].status == STAT_OK)
	nok++;
    }

  if (nok == nthreads)
    pthread_cancel (hthread);
  else
    pthread_join (hthread, NULL);



  time (&t_finish);
  if ((diff_sec = t_finish - t_start) == 0)
    diff_sec = 1;		/* Avoid division by zero       */

  Log ("Download completed, job completed in %d seconds. (%d Kb/sec)",
       diff_sec, ((req->clength - h->bwritten) / diff_sec) / 1024);
  Log ("Shutting down...");
  close (fd);
}



/************************************************************************************
 *
 *   Resume.c
 *
 ************************************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>


extern struct thread_data *wthread;
extern struct request *req;
extern int nthreads;
extern int bwritten;


void
save_log ()
{
  char *logfile;
  struct hist_data h;
  FILE *fp;

  logfile = (char *) malloc (255 *sizeof (char));
  memset(logfile, 0, 255);
  


  if (strlen (req[0].lfile) == 0)
    snprintf (logfile, 255, "aget-%s.log", req[0].file);
  else
    snprintf (logfile, 255, "aget-%s.log", req[0].lfile);

  if ((fp = fopen (logfile, "w")) == NULL)
    {
      fprintf (stderr, "cannot open log file %s for writing: %s\n", logfile,
	       strerror (errno));
      exit (1);
    }


  memcpy (&(h.req), req, sizeof (struct request));
  memcpy (&(h.wthread), wthread, sizeof (struct thread_data) * nthreads);
  h.nthreads = nthreads;
  h.bwritten = bwritten;

  printf ("--> Logfile is: %s, so far %d bytes have been transferred\n",
	  logfile, h.bwritten);

  fwrite (&h, sizeof (struct hist_data), 1, fp);
  fclose (fp);

  free (logfile);
}


int
read_log (struct hist_data *h)
{
  char *logfile;
  FILE *fp;

  logfile = (char *) malloc (255 * sizeof (char));
  memset(logfile, 0, sizeof(char) * 255);


  if (strlen (req[0].lfile) == 0)
    snprintf (logfile, 255, "aget-%s.log", req[0].file);
  else
    snprintf (logfile, 255, "aget-%s.log", req[0].lfile);

  Log ("Attempting to read log file %s for resuming download job...",
       logfile);

  if ((fp = fopen (logfile, "r")) == NULL)
    {
      if (errno == ENOENT)
	{
	  Log
	    ("Couldn't find log file for this download, starting a clean job...");
	  return -1;
	}
      else
	{
	  fprintf (stderr, "cannot open log file %s for reading: %s\n",
		   logfile, strerror (errno));
	  exit (1);
	}
    }

  fread (h, sizeof (struct hist_data), 1, fp);
  bwritten = h->bwritten;
  fclose (fp);

  Log ("%d bytes already transferred", bwritten);

  /* Unlinking logfile after we've read it        */
  if ((unlink (logfile)) == -1)
    fprintf (stderr, "read_log: cannot remove stale log file %s: %s\n",
	     logfile, strerror (errno));

  free (logfile);

  return 0;
}


/************************************************************************************
 *
 *   Download.c
 *
 ************************************************************************************/


#define _XOPEN_SOURCE 500


#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <netdb.h>
#include <time.h>
#include <signal.h>
#include <pthread.h>

#include <netinet/in.h>

#include <sys/types.h>

#include <arpa/inet.h>

#include <sys/socket.h>


extern sigset_t signal_set;


extern int errno;

int bwritten = 0;
pthread_mutex_t bwritten_mutex;

void *
http_get (void *arg)
{
  struct thread_data *td;
  int sd;
  char *rbuf, *s;
  int dr, dw, i;
  long foffset;
  pthread_t tid;
  tid = pthread_self ();

  /* Block out all signals        */
  pthread_sigmask (SIG_BLOCK, &signal_set, NULL);

  /* Set Cancellation Type to Asynchronous        */
  pthread_setcanceltype (PTHREAD_CANCEL_ASYNCHRONOUS, NULL);

  td = (struct thread_data *) arg;

  foffset = td->foffset;

  rbuf = (char *) malloc (GETRECVSIZ * sizeof (char) );
  memset(rbuf, 0, sizeof(char) * GETRECVSIZ);


  if ((sd = socket (AF_INET, SOCK_STREAM, 0)) == -1)
    {
      Log ("<THREAD #%ld> socket creation failed: %s", tid, strerror (errno));
      pthread_exit ((void *) 1);
    }

  if ((connect
       (sd, (const struct sockaddr *) &td->sin,
	sizeof (struct sockaddr))) == -1)
    {
      Log ("<THREAD #%ld> connection failed: %s", tid, strerror (errno));
      pthread_exit ((void *) 1);
    }

  if ((send (sd, td->getstr, strlen (td->getstr), 0)) == -1)
    {
      Log ("<THREAD #%ld> send failed: %s", tid, strerror (errno));
      pthread_exit ((void *) 1);
    }

  if ((dr = recv (sd, rbuf, GETRECVSIZ, 0)) == -1)
    {
      Log ("<THREAD #%ld> recv failed: %s", tid, strerror (errno));
      pthread_exit ((void *) 1);
    }

  handleHttpRetcode (rbuf);

  if ((strstr (rbuf, "HTTP/1.1 206")) == NULL)
    {
      fprintf (stderr, "Something unhandled happened, shutting down...\n");
      exit (1);
    }

  s = rbuf;
  i = 0;
  while (1)
    {
      if (*s == '\n' && *(s - 1) == '\r' && *(s - 2) == '\n'
	  && *(s - 3) == '\r')
	{
	  s++;
	  i++;
	  break;
	}
      s++;
      i++;
    }
  td->offset = td->soffset;

  if ((dr - i) > foffset)
    dw = pwrite (td->fd, s, (foffset - i), td->soffset);
  else
    dw = pwrite (td->fd, s, (dr - i), td->soffset);
  td->offset = td->soffset + dw;


  pthread_mutex_lock (&bwritten_mutex);
  bwritten += dw;
  pthread_mutex_unlock (&bwritten_mutex);

  while (td->offset < foffset)
    {
      memset (rbuf, GETRECVSIZ, 0);
      dr = recv (sd, rbuf, GETRECVSIZ, 0);
      if ((td->offset + dr) > foffset)
	dw = pwrite (td->fd, rbuf, foffset - td->offset, td->offset);
      else
	dw = pwrite (td->fd, rbuf, dr, td->offset);
      td->offset += dw;
      pthread_mutex_lock (&bwritten_mutex);
      bwritten += dw;
      pthread_mutex_unlock (&bwritten_mutex);
      updateProgressBar (bwritten, td->clength);
    }

  if (td->offset == td->foffset)
    td->status = STAT_OK;	/* Tell thet download is OK.    */

  close (sd);

/*        printf("<THREAD #%ld> Part %d completed, leaving thread...\n", tid, td->tind);*/
  pthread_exit (NULL);
  return NULL;
}




/************************************************************************************
 *
 *  Signal.c
 *
 ************************************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <pthread.h>
#include <unistd.h>


extern int nthreads;
extern struct thread_data *wthread;
extern struct request *req;
extern int bwritten;
extern pthread_mutex_t bwritten_mutex;

void *
signal_waiter (void *arg)
{
  int signal;

  arg = NULL;

  pthread_sigmask (SIG_UNBLOCK, &signal_set, NULL);

  while (1)
    {
#ifdef SOLARIS
      sigwait (&signal_set);
#else
      sigwait (&signal_set, &signal);
#endif
      switch (signal)
	{
	case SIGINT:
	  sigint_handler ();
	  break;
	case SIGALRM:
	  sigalrm_handler ();
	  break;
	}
    }
}

void
sigint_handler (void)
{
  int i;

  printf ("^C caught, saving download job...\n");

  for (i = 0; i < nthreads; i++)
    {
      pthread_cancel (wthread[i].tid);
      wthread[i].status &= STAT_INT;	/* Interrupted download */
    }

  save_log ();

  exit (0);
}


void
sigalrm_handler (void)
{
  printf ("Signal Alarm came\n");
  updateProgressBar (bwritten, req->clength);
  alarm (1);
}


/************************************************************************************
 *
 *   Head.c
 *
 ************************************************************************************/


#define _XOPEN_SOURCE 500


#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <netdb.h>
#include <time.h>
#include <pthread.h>


#include <sys/types.h>
#include <sys/socket.h>

#include <arpa/inet.h>
#include <netinet/in.h>

#ifdef SOLARIS
#include <arpa/nameser.h>
#include <resolv.h>
#endif


extern int errno;
extern int h_errno;


void
http_head_req (struct request *req)
{
  struct sockaddr_in sin;
  struct hostent *he;
  int sd;
  char *sbuf;
  char *rbuf;
  char *tok;
  char *s;
  int clength;


  sbuf = (char *) malloc ((HEADREQSIZ + strlen (req->url)) * sizeof (char));
  memset(sbuf, 0, (HEADREQSIZ + strlen (req->url)) * sizeof (char));

  rbuf = (char *) malloc (HEADREQSIZ * sizeof (char) );
  memset(rbuf, 0, HEADREQSIZ * sizeof (char));
			   
  if ((he = gethostbyname (req->host)) == NULL)
    {
      Log ("Error: Cannot resolve hostname for %s: %s",
	   req->host, hstrerror (h_errno));
      exit (1);
    }
  strncpy (req->ip, inet_ntoa (*(struct in_addr *) he->h_addr), MAXIPSIZ);


  time (&t_start);
  bzero (&sin, sizeof (sin));
  sin.sin_family = AF_INET;
  sin.sin_addr.s_addr = inet_addr (req->ip);
  sin.sin_port = htons (req->port);

  if ((sd = socket (AF_INET, SOCK_STREAM, 0)) == -1)
    {
      Log ("Socket creation failed for Head Request: %s", strerror (errno));
      exit (1);
    }
  if ((connect (sd, (const struct sockaddr *) &sin, sizeof (sin))) == -1)
    {
      Log ("Connection failed for Head Request: %s", strerror (errno));
      exit (1);
    }
  Log ("Head-Request Connection established");

  sprintf (sbuf, HEADREQ, req->url, req->host, PROGVERSION);
  if ((send (sd, sbuf, strlen (sbuf), 0)) == -1)
    {
      Log ("send failed for Head Request: %s", strerror (errno));
      exit (1);
    }

  if ((recv (sd, rbuf, HEADREQSIZ, 0)) == -1)
    {
      Log ("recv failed for Head Request: %s", strerror (errno));
      exit (1);
    }

  handleHttpRetcode (rbuf);

  tok = strtok (rbuf, "\r\n");
  if ((strstr (tok, "HTTP/1.1 200")) != NULL)
    {
      while ((tok = strtok (NULL, "\r\n")) != NULL)
	{
	  if ((strstr (tok, "Content-Length")) != NULL)
	    {
	      s = (tok + strlen ("Content-Length: "));
	      clength = atoi (s);
	      req->clength = clength;
	    }
	}
    }
  free (sbuf);
  free (rbuf);

}








/*************************************************************************************
 * 
 *   Misc.c
 * 
 *************************************************************************************/


#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <strings.h>
#include <errno.h>

#include <sys/stat.h>
#include <sys/types.h>

void
parse_url (char *url, struct request *req)
{
  char *s;
  int i, j, k;

  i = j = k = 0;
  s = url;
  if ((strncmp (url, "ftp://", 6)) == 0)
    {
      fprintf (stderr,
	       "Error: Currently Aget doesn't support FTP requests...\n");
      exit (1);
    }
  else if ((strncmp (url, "http://", 7)) != 0)
    {
      fprintf (stderr, "Error: URL should be of the form http://...\n");
      exit (1);
    }

  if (req->port == 0)
    {
      req->port = 80;
      req->proto = PROTO_HTTP;
    }


  s = url + 7;			/* Jump pass http:// part       */
  for (i = 0; *s != '/'; i++, s++)
    {
      if (i > MAXHOSTSIZ)
	{
	  fprintf (stderr, "Error: Cannot get hostname from URL...\n");
	  exit (1);
	}
      if (*s == ':')
	{			/* If user/pass is supplied like; http://murat:12345@x.y.com/url.html */
	  while (*s != '/')
	    {
	      req->username[j++] = *--s;
	      i--;
	    }
	  req->username[--j] = '\0';
	  revstr (req->username);
	  while (1)
	    {
	      if (*s == ':')
		{
		  while (*s != '@')
		    {
		      if (k > MAXBUFSIZ)
			{
			  fprintf (stderr,
				   "Error: Cannot get password from URL...\n");
			  exit (1);
			}
		      req->password[k++] = *++s;
		    }
		  break;
		}
	      s++;
	    }
	  req->password[--k] = '\0';
	}
      req->host[i] = *s;
    }
  req->host[i] = '\0';
  for (i = 0; *s != '\0'; i++, s++)
    {
      if (i > MAXURLSIZ)
	{
	  fprintf (stderr,
		   "Error: Cannot get remote file name from URL...\n");
	  exit (1);
	}
      req->url[i] = *s;
    }
  req->url[i] = '\0';
  --s;
  for (i = 0; *s != '/'; i++, s--)
    {
      if (i > MAXBUFSIZ)
	{
	  fprintf (stderr, "Error: Cannot get local file name from URL...\n");
	  exit (1);
	}
      req->file[i] = *s;
    }
  req->file[i] = '\0';
  revstr (req->file);

}

int
numofthreads (int size)
{
  return 2;
/*   if (size == 0) */
/*     return 0; */
/*   else if (size < BUFSIZ * 2)	/\* < 16384 *\/ */
/*     return 1; */
/*   else if ((size >= BUFSIZ * 2) && (size < BUFSIZ * 4))	/\* 16384 < x < 32678    *\/ */
/*     return 2; */
/*   else if ((size >= BUFSIZ * 4) && (size < BUFSIZ * 8))	/\* 32768 < x < 65536    *\/ */
/*     return 3; */
/*   else if ((size >= BUFSIZ * 8) && (size < BUFSIZ * 16))	/\* 65536 < x < 131072   *\/ */
/*     return 4; */
/*   else if ((size >= BUFSIZ * 16) && (size < BUFSIZ * 32))	/\* 131072 < x < 262144  *\/ */
/*     return 5; */
/*   else if ((size >= BUFSIZ * 32) && (size < BUFSIZ * 64)) */
/*     return 6; */
/*   else if ((size >= BUFSIZ * 64) && (size < BUFSIZ * 128)) */
/*     return 7; */
/*   else if ((size >= BUFSIZ * 128) && (size < BUFSIZ * 256)) */
/*     return 8; */
/*   else if ((size >= BUFSIZ * 256) && (size < BUFSIZ * 512)) */
/*     return 9; */
/*   else */
/*     return 10; */
}

int
calc_offset (int total, int part, int nthreads)
{
  return (part * (total / nthreads));
}


void
usage ()
{
  fprintf (stderr, "usage: aget [options] url\n");
  fprintf (stderr, "\toptions:\n");
  fprintf (stderr, "\t\t-p port number\n");
  fprintf (stderr, "\t\t-l local file name\n");
  fprintf (stderr, "\t\t-n suggested number of threads\n");
  fprintf (stderr, "\t\t-f force using suggested number of threads\n");
  fprintf (stderr, "\t\t-h this screen\n");
  fprintf (stderr, "\t\t-v version info\n");
  fprintf (stderr, "\n");
  fprintf (stderr, "http//www.enderunix.org/aget/\n");
}

/* reverse a given string	*/
void
revstr (char *str)
{
  char *p, *s;
  int i;
  int size;

  if ((size = strlen (str)) == 0)
    return;
  p = (char *) malloc (size * sizeof (char));
  memset(p, 0, sizeof(char) * size);

  s = p;
  for (i = size; i >= 0; i--, s++)
    *s = *(str + i - 1);
  *s = '\0';
  memset (str, 0, size);
  strncpy (str, p, size);
  free (p);
}

/* Log	*/
void
Log (char *fmt, ...)
{
  va_list ap;
  char *lfmt;

  lfmt = (char *) malloc ((7 + strlen (fmt)) * sizeof (char));
  memset(lfmt, 0, 7+ strlen(fmt));

  sprintf (lfmt, "<LOG> %s", fmt);

  fflush (stdout);
  va_start (ap, fmt);
  vfprintf (stderr, lfmt, ap);
  va_end (ap);

  if (fmt[0] != '\0' && fmt[strlen (fmt) - 1] == ':')
    fprintf (stderr, " %s", strerror (errno));
  fprintf (stderr, "\n");
  free (lfmt);
}

/* Progress Bar	*/
void
updateProgressBar (float cur, float tot)
{
  float rat;
  int ndot, i;
  static float prev = -1;

  rat = cur / tot;
  ndot = (int) (rat * 100);

  if ((ndot < prev + 5) && (ndot != 100))
    return;

  for (i = 0; i < ndot; i += 2)
    putchar ('.');
  for (i = ndot - 1; i < 100; i += 2)
    putchar (' ');
  printf ("[%d%% completed]\n", ndot);
  prev = ndot;
}

void
handleHttpRetcode (char *rbuf)
{

  if ((strstr (rbuf, "HTTP/1.1 416")) != NULL)
    {
      Log
	("Server returned HTTP/1.1 416 - Requested Range Not Satisfiable\n");
      exit (1);
    }
  else if ((strstr (rbuf, "HTTP/1.1 403")) != NULL)
    {
      Log ("<Server returned HTTP/1.1 403 - Permission Denied\n");
      exit (1);
    }
  else if ((strstr (rbuf, "HTTP/1.1 404")) != NULL)
    {
      Log ("<Server returned HTTP/1.1 404 - File Not Found\n");
      exit (1);
    }
}




int  main (int argc, char **argv)
{
  extern char *optarg;
  extern int optind;
  int c, error = 0, ret;
  struct hist_data h;
  int retlog;

  pthread_mutex_init(&bwritten_mutex, 0);

  /* Allocate heap for download request   
   * struct request stores all the information that might be
   * of interest
   */
  req = (struct request *) malloc (1 * sizeof (struct request));
  memset(req, 0, sizeof(struct request));

  
  /* Only some signals will be emitted    */
/*   sigemptyset (&signal_set); */
/*   sigaddset (&signal_set, SIGINT); */
/*   sigaddset (&signal_set, SIGALRM); */
  
  /* Block out all signals        */
/*   pthread_sigmask (SIG_BLOCK, &signal_set, NULL); */
  
  /* Create a thread for hadling signals  */
/*   if ((ret = pthread_create (&hthread, NULL, signal_waiter, NULL)) != 0){ */
/*     fprintf (stderr, "main: cannot create signal_waiter thread: %s, exiting...\n", */
/* 	     strerror (errno)); */
/*     exit (-1); */
/*   } */
  
  while (!error && (c = getopt (argc, argv, "p:l:n:hfv")) != -1){
    switch (c){
    case 'p':   req->port = atoi(optarg);  break;
    case 'f':   fsuggested = 1;  break;
    case 'l':   strncpy (req->lfile, optarg, MAXBUFSIZ);  break;
    case 'n':
      if ((nthreads = atoi (optarg)) > MAXTHREADS) {
	Log ("Error: Maximum # of threads allowed is %d\n", MAXTHREADS);
	nthreads = 0;
      }
      break;

    case 'h':
	  printf ("%s\n", PROGVERSION);
	  usage ();
	  exit (0);
	  break;
	case 'v':
	  printf ("%s\nby Murat BALABAN <murat@enderunix.org>\n",
		  PROGVERSION);
	  exit (0);
	  break;
	default:
	  error = 1;
	  usage ();
	  exit (1);
	  break;
	}
    }

  if (error){
    usage ();
    exit (1);
  }

  if (fsuggested == 1 && nthreads == 0) {
      fprintf (stderr,
	       "\nERROR: -f and -n should be used together!, exiting...\n\n");
      usage ();
      exit (1);
    }

  if (argc == 2)		/* If only url is supplied...   */
    fullurl = strdup (argv[1]);
  else if (optind < argc)
    if (argc > 2)
      fullurl = strdup (argv[optind]);
    else
      {
	usage ();
	exit (1);
      }
  else if (optind == argc)
    {
      usage ();
      exit (1);
    }

  parse_url (fullurl, req);

  /* If a log file for a previous try has been found, read it and
   * resume the download job (resume_get), otherwise, start with
   * a clean job (get) 
   *
   * Logfile is of the pattern: aget-$file_name.log
   */
  if ((retlog = read_log (&h)) != -1)
    resume_get (&h);
  else
    get (req);

  return 0;
}
