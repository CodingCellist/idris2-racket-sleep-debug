CC = gcc
CFLAGS = -Wall -Wextra -Werror -fpic

.PHONY: clean

all: foreign_sleep.o foreign_sleep.so

foreign_sleep.o: foreign_sleep.c
	$(CC) -c -o $@ $(CFLAGS) $^

foreign_sleep.so: foreign_sleep.o
	$(CC) -shared -o $@ $^

clean:
	$(RM) *.o *.so

