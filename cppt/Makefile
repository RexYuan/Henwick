
default: minisat.hxx.gch bf.o ctx.hxx misat.cxx
	g++-10 -std=c++20 bf.o misat.cxx -I. -L. -lminisat -o m && ./m

bf.o: bf.cxx bf.hxx
	g++-10 -std=c++20 -c bf.cxx -I. -L. -lminisat -o bf.o

minisat.hxx.gch: minisat.hxx
	g++-10 -std=c++20 -c minisat.hxx -I.

clean:
	trash m
	trash *.o
	trash *.gch
