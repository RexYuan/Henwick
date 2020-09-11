
#include <iostream>
#include <algorithm>
#include <bitset>
#include <functional>
#include <vector>
#include <variant>
#include <memory>
#include <string>

#include "minisat.hxx"

#include "bf.hxx"
#include "ctx.hxx"

using namespace Minisat;
using namespace std;

namespace exposer
{
    using ctx = Ctx<2>;

    using Bv = ctx::Bv;
    using Face = ctx::Face;
    
    auto& mkBv = ctx::mkBv;
    auto& mkBvs = ctx::mkBvs;
    auto& to_string = ctx::to_string;
}

int main()
{
    using namespace exposer;

    Ctx<2> c;
    c.init_cdnf();

    Face f1 ("00", {"10","01"});

    Face f2 {"11"};
    f2.primes = mkBvs({"10"});
    f2.push("01");

    vector<Face> cdnf {f1,f2};
    c.add_cdnf(cdnf);

    c.tabulate();

/*
    Solver s2;
    s2.newVar();
    s2.newVar();
    s2.newVar();
    s2.newVar();
    //s.addClause(~mkLit(0), mkLit(1));
    //s.addClause(~mkLit(0), ~mkLit(1));
    Bf_ptr b = (v(0) > v(1)) &
               (v(1) > v(0)) &
               (v(1) > v(2));
    cout << b;
    Var v = addBf(s2, b);
    s2.addClause(mkLit(v));
    
    Ctx<3>::tabulate(s2);*/
}