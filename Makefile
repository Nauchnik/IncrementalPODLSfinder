CPP = g++
INC1 = ../DiagonalLatinSquaresGenerator/
INCDIRS = -I${INC1}
CPPFLAGS = -O3 -std=c++0x ${INCDIRS} -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS

PODLS_CNF_creator: main.o odls_sequential.o
	${CPP} ${CPPFLAGS} main.o odls_sequential.o -o PODLS_CNF_creator

odls_sequential.o: ../DiagonalLatinSquaresGenerator/odls_sequential.cpp
	${CPP} ${CPPFLAGS} ../DiagonalLatinSquaresGenerator/odls_sequential.cpp -c

main.o: main.cpp
	${CPP} ${CPPFLAGS} main.cpp -c

clean:
	rm -rf *.o
	rm PODLS_CNF_creator
	clear