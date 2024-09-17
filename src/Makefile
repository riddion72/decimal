OS=$(shell uname)
CC=gcc
CFLAGS = -std=c11 -Werror -Wextra -Wall -g
ifeq ($(OS), Darwin)
 CHECK= -lcheck -lpthread -lm
else
 CHECK= -lcheck -lpthread -lm -lsubunit
endif
SOURCE = s21_*.c tests/*.c
SRC = $(wildcard s21_*.c)

all: main

main: s21_decimal.a test

s21_decimal.o:
	$(CC) $(CFLAGS) -c $(SRC)

s21_decimal.a: s21_decimal.o
	ar rcs s21_decimal.a s21_*.o
	ranlib s21_decimal.a

test: s21_decimal.a
	$(CC) $(CFLAGS) tests/*.c s21_decimal.a $(CHECK) -o test -lcheck
	./test

rebuild: clean all

gcov_report: s21_decimal.o s21_decimal.a
	$(CC) $(CFLAGS) --coverage $(SOURCE) s21_decimal.a -L. s21_decimal.a $(CHECK) -o ./test 
	./test
	mkdir report
	lcov -t "test" -o test.info -c -d .
	genhtml -o report test.info
	open report/index.html
	rm -rf *.gcda *.gcno *.out *.o

check:
	clang-format -style=Google -i *.c *.h tests/*.c tests/*.h
	clang-format -style=Google -n *.c *.h tests/*.c tests/*.h
	leaks --atExit -- ./test

clean:
	rm -rf *.o *.gcda *.gcno *.a *.out *.info *.dSYM report test
