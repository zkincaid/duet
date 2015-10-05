#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define NUM_THREADS     4
#define MASTER_ID       0
#define MAX_POINTS 10000000
#define RADIUS 500
#define SQR_RADIUS RADIUS*RADIUS

typedef struct ThreadData{
        pthread_t thread;
        int threadId;
        unsigned long numHits;
        unsigned long numPoints;
        struct ThreadData *threadDataList;
    } ThreadData;


 void *calculatePI(void *threadData){

     ThreadData *data = (ThreadData*)threadData;

     unsigned long x,y;

     srand(time(NULL));

     while(data->numPoints!=MAX_POINTS){

        x = rand()%(RADIUS+1);
        y = rand()%(RADIUS+1);

        if( (x*x + y*y) < SQR_RADIUS)
           data->numHits++;

        data->numPoints++;
     }


     if(data->threadId == MASTER_ID){

        int i;

        for(i=0;i<NUM_THREADS;++i)
           if(i!=MASTER_ID)
              pthread_join(data->threadDataList[i].thread,NULL);


        unsigned long totalHits=0,totalPoints=0;

        for(i=0;i<NUM_THREADS;++i){
           totalHits+= data->threadDataList[i].numHits;
           totalPoints+= data->threadDataList[i].numPoints;
        }

        printf("Numeros de pontos: %d, numero de acertos: %d\n",totalPoints, totalHits);

        printf("Valor de Pi com 81 casas decimais: %.8lf\n",(4*((double)totalHits/(double)totalPoints)));

     }

     printf("Thread %d terminou\n",data->threadId);
}

int main (int argc, char *argv[])
{

   pthread_attr_t attr;
   ThreadData threads[NUM_THREADS];
   int i;

   threads[MASTER_ID].threadDataList = &threads[0];
   pthread_attr_init(&attr);
   pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

   printf("Calculando o valor de Pi pelo algoritmo de Monte Carlo: \n");

   for(i=0;i<NUM_THREADS;++i){
      threads[i].threadId = i;
      threads[i].numHits = 0;
      threads[i].numPoints =0;
      pthread_create(&threads[i].thread,&attr,calculatePI,(void*) &threads[i]);
   }

   pthread_attr_destroy(&attr);
   pthread_join(threads[MASTER_ID].thread,NULL);
   pthread_exit(NULL);

   return 0;
}
