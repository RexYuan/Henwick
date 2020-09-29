
default: minisat.hxx.gch bf.o dlearn.hxx blearn.hxx ctx.hxx main.cxx
	g++-10 -std=c++20 bf.o main.cxx -I. -L. -lminisat -o out.o && ./out.o

bf.o: bf.cxx bf.hxx
	g++-10 -std=c++20 -c bf.cxx -I. -L. -lminisat -o bf.o

minisat.hxx.gch: minisat.hxx
	g++-10 -std=c++20 -c minisat.hxx -I.

clean:
	trash *.o
	trash *.gch
