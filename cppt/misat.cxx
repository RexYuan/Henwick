
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

using namespace exposer;

void t1()
{
    Ctx<2> c(Mode::States);

    Face f1 ("00", {"10","01"});
    Face f2 ("11", {"10","01"});
    vector<Face> cdnf {f1,f2};

    Var f, fp;
    tie(f, fp) = c.tryCdnf(cdnf);
    c.s.addClause(mkLit(f));
    c.s.addClause(mkLit(fp));
    //c.tryClause(mkLit(f));
    //c.tryClause(mkLit(fp));
    
    Var b = c.tryBf(v(0) > v(2) & v(1) != v(3));
    //c.s.addClause(mkLit(b));
    c.tryClause(mkLit(b));

    c.tabulate();
    c.forget();
    c.tryClause(mkLit(b));
    c.tabulate();
}

void t2()
{
    Ctx<3> c(Mode::Vars);

    Bf_ptr b = (v(0) > v(1)) &
               (v(1) > v(0)) &
               (v(1) > v(2));
    Var v = c.addBf(b);

    c.tryClause(mkLit(v));
    c.tabulateVars();
}

int main()
{
    t1();
    //f<ff>(2);
}