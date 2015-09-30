#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>
#include <string.h>

#define CPUS 1
#define BUFF_SIZE 150

struct par_arg {
    char *fname;
    char *o_buff; //output buffer.
    int start;
    int stop;
    int thread;
    int written; // Number of bytes written.
};

/* A very unsmart function to parse logs */
int parse_line( void *args, char *line, int len) {
    char dig;
    int i;
    if(line[31] == 'A'){
        //printf("ACK\n");
        // timestap plus extra space
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, line, 16);
        ((struct par_arg*)args)->written += 16;
        // "ACK "
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, "ACK ", 4);
        ((struct par_arg*)args)->written += 4;
        // IP - ip start on character 38
        for( i= 38, dig = line[i] ; dig != ' ' ; i++, dig = line[i] ){
            continue;
        }
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, line+38, i-37 );
        ((struct par_arg*)args)->written += i-37; // We want to catch the extra space

        // Mac 
        // we stopped at space after ip. Add four bytes and we are at mac.
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, line+i+4, 17);
        ((struct par_arg*)args)->written += 17; //12 hex + 5 colons
        ((struct par_arg*)args)->o_buff[((struct par_arg*)args)->written] = '\n';
        ++((struct par_arg*)args)->written;
    } else if( line[31] == 'N' ){
        //printf("NAK\n");
        // timestap plus extra space
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, line, 16);
        ((struct par_arg*)args)->written += 16;
        // "ACK "
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, "NAK ", 4);
        ((struct par_arg*)args)->written += 4;
        // IP - ip start on character 38
        for( i= 38, dig = line[i] ; dig != ' ' ; i++, dig = line[i] ){
            continue;
        }
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, line+38, i-37 );
        ((struct par_arg*)args)->written += i-37; // We want to catch the extra space

        // Mac 
        // we stopped at space after ip. Add four bytes and we are at mac.
        memcpy(((struct par_arg*)args)->o_buff + ((struct par_arg*)args)->written, line+i+4, 17);
        ((struct par_arg*)args)->written += 17; //12 hex + 5 colons
        ((struct par_arg*)args)->o_buff[((struct par_arg*)args)->written] = '\n';
        ++((struct par_arg*)args)->written;
    }else{
        //memcpy(((struct par_arg*)args)->written + ((struct par_arg*)args)->o_buff, line, strlen(line));
        //((struct par_arg*)args)->written += len;
    }
}

void * parse_lines( void * args ) {
    FILE *fp = fopen(((struct par_arg*)args)->fname, "r");
    if (fp < 0){
        perror("I Don't know what is going on.\n");
        exit(1);
    }
    int start = ((struct par_arg*)args)->start;
    int stop = ((struct par_arg*)args)->stop;
    int thread = ((struct par_arg*)args)->thread;

    char line[BUFF_SIZE];
    size_t len;
    fseek( fp, start, SEEK_SET );
    if( start != 0 ){ // We need the start thread to just start.
        while ( fgetc( fp ) != '\n' ) {
            start++;
        }
        start++;  // fp points at new line. Move one up.
    }

    while( fgets( line, BUFF_SIZE, fp ) != NULL && start < stop ) {
        len = strlen( line );
        //printf("%d = line is: %s\n",thread,line);
        parse_line( args, line , len);
        start += len;
    }
}


int main( int argc, char **argv ) {
    FILE *in_file;
    FILE *out_file;
    char *fname;
    int f_size;
    int chunk_size;
    int i, start, stop, st;
    void *status;
    struct par_arg par_arg[CPUS];

    /*
        File Stuff
    */
    if(argc > 1){
        fname = argv[1];
        fprintf(stdout, "Filename is %s\n", fname);
    } else {
        exit(1);
    }
    in_file = fopen(fname, "r");
    out_file = fopen("status", "w+");

    // Grab size of file
    i = fseek( in_file, 0, SEEK_END);
    if ( i < 0 ){
        printf("Shit\n");
    }
    f_size = ftell( in_file );
    i = fseek(in_file,0,SEEK_SET);
    printf("File size: %d\n",f_size);
    chunk_size = f_size / CPUS;
    printf("chuck_size size: %d\n",chunk_size);


    /* Pthread stuff */
    pthread_t threads[CPUS];
    pthread_attr_t attr;


    /* We want to joni these threads later. */
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

    for ( i=0 ; i < CPUS ; i++ ) {
        par_arg[i].start = i*chunk_size;
        par_arg[i].stop = (i+1)*chunk_size - 1;
        par_arg[i].fname = fname;
        par_arg[i].o_buff = (char *)malloc(chunk_size);
        par_arg[i].thread = i;
        par_arg[i].written = 0;
        printf("CPU %i: starting at %d, ending at %d\n", i,i*chunk_size, (i+1)*chunk_size - 1);
        //parse_lines( in_file, start, stop );
        st = pthread_create (&threads[i], &attr, parse_lines, (void *)&par_arg[i]);
        if (st){
            printf("ERROR; return code from pthread_create() is %d\n", st);
            exit(-1);
        }
    }

    // end threads
    pthread_attr_destroy(&attr);
    fseek(out_file, 0, SEEK_SET);
    for(i=0; i < CPUS; i++) {
        st = pthread_join(threads[i], &status);
        if (st) {
            printf("ERROR; return code from pthread_join() is %d\n", st);
            exit(-1);
        }
        printf("Main: completed join with thread %ld having a status of %ld\n",(long)i,(long)status);
//        printf("%i = %s",(int)i,par_arg[i].o_buff);
        fwrite( par_arg[i].o_buff, 1, par_arg[i].written, out_file );
    }

    printf("Crunched\n");
}
