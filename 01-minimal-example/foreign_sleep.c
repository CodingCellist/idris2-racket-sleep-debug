#include "foreign_sleep.h"

void fsleep(int sec) {
    struct timespec t;
    t.tv_sec = sec;
    t.tv_nsec = 0;

    nanosleep(&t, NULL);
}

