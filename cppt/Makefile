
.PHONY: all build run clean test
.DEFAULT_GOAL := all

CXX := g++-10
CXXFLAGS := -std=c++20 -I. -L. -lminisat
HXXFLAGS := -std=c++20 -I.

ALGOS := dlearn.hxx blearn.hxx
HELPERS := misc.hxx state.hxx switch.hxx ctx.hxx

MINISAT := minisat.hxx.gch
OBJS := bf.o
HDRS := $(ALGOS) $(HELPERS)
MAIN := main.cxx
DEP := $(MINISAT) $(OBJS) $(HDRS) $(MAIN)

all: $(DEP)
	$(CXX) $(CXXFLAGS) $(OBJS) $(MAIN) -o out.o && ./out.o

build: $(DEP)
	$(CXX) $(CXXFLAGS) $(OBJS) $(MAIN) -o out.o

run: build
	./out.o

bf.o: bf.cxx bf.hxx
	$(CXX) $(CXXFLAGS) -c bf.cxx -o bf.o

minisat.hxx.gch: minisat.hxx
	$(CXX) $(HXXFLAGS) -c minisat.hxx

clean:
	trash *.o
	trash *.gch

test: test.cxx
	$(CXX) $(CXXFLAGS) test.cxx -o test.o && ./test.o