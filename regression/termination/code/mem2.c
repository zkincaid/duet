void *malloc(int);
void usage(int x) {
    exit(x);
}
void main(int argc, char* argv[]){
    int optind;
    char **files;
    int n_files;
    assume(argc >= 0);
    argv = malloc(argc * sizeof(char*));
    optind = 1;

    n_files = argc - optind;
    files = argv + optind;
    if (n_files <= 0) {
	usage(1);
    }

    char c = files[0];
}
