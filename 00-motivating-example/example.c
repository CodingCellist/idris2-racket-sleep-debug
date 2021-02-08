#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <pthread.h>
#include <errno.h>

void* child(void* arg)
{
    struct timespec t;
    t.tv_sec = 1;
    t.tv_nsec = 0;

    int s1 = nanosleep(&t, NULL);
    if (s1) perror("child:sleep1");

    printf("Wor\n");

    t.tv_sec = 2;
    int s2 = nanosleep(&t, NULL);
    if (s2) perror("child:sleep2");
    return NULL;
}

int main(void)
{
    // stuff we will need
    pthread_t* child_thread = calloc(1, sizeof(pthread_t));
    struct timespec t;

    // start of main
    printf("Hello\n");

    int cRes = pthread_create(child_thread, NULL, &child, NULL);
    if (cRes) perror("main:pthread_create");

    t.tv_sec = 4;
    t.tv_nsec = 0;
    
    int c4 = nanosleep(&t, NULL);
    if (c4) perror("main:sleep4");

    printf("ld\n");

    t.tv_sec = 5;
    int c5 = nanosleep(&t, NULL);
    if (c5) perror("main:sleep5");

    return 0;
}

