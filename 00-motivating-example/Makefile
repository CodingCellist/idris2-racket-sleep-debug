CC = gcc
CFLAGS = -pthread
LFLAGS = -pthread

.PHONY: clean

all: example

example: example.o
	$(CC) -o $@ $(LFLAGS) $^

example.o: example.c
	$(CC) -c -o $@ $(CFLAGS) $^

clean:
	$(RM) *.o example

