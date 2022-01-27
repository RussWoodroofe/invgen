CFLAGS="-Os"

all: invgen_sievelp

invgen_sievelp: invgen_sievelp.o
	cc -o invgen_sievelp invgen_sievelp.o -lprimesieve

tgz: *.c batchjob Makefile
	rm invgen.tgz
	tar cvzf invgen.tgz batchjob *.c Makefile
