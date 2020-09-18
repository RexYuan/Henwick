
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
#include "learn.hxx"

using namespace Minisat;
using namespace std;

namespace exposer
{
    using ctx = Ctx<3>;

    using Bv = ctx::Bv;
    using Face = ctx::Face;
    using FaceVector = ctx::FaceVector;
    //using Learner = ctx::Learner;
    
    auto& mkBv = ctx::mkBv;
    auto& mkBvs = ctx::mkBvs;
    auto& to_string = ctx::to_string;
    auto& printFace = ctx::printFace;
    auto& printFaces = ctx::printFaces;
}

using namespace exposer;

void t1()
{
    Ctx<2> c(Mode::States);

    Ctx<2>::Face f1 ("00", {"10","01"});
    Ctx<2>::Face f2 ("11", {"10","01"});
    Ctx<2>::FaceVector cdnf {f1,f2};

    Var f, fp;
    tie(f, fp) = c.tryCdnf(cdnf);
    c.addClause(mkLit(f));
    c.addClause(mkLit(fp));
    //c.tryClause(mkLit(f));
    //c.tryClause(mkLit(fp));
    
    Var b = c.addBf((v(0) |= v(2)) & (v(1) != v(3)));
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

    Bf_ptr b = (v(0) |= v(1)) &
               (v(1) |= v(0)) &
               (v(1) |= v(2));
    //Var v = c.addBf(b);
    Var v = c.tryBf(b);

    c.tryClause(mkLit(v));
    c.tabulate();
    c.forget();
    c.tryClause(~mkLit(v));
    c.tabulate();
}

void t3()
{
    ctx c(Mode::States);

    // trans: totally connected component
    // 00 - bads
    // 01 -
    // ---
    // 10 -
    // 11 - inits
    
    Bf_ptr inits = v(0),
           bads = ~v(0),
           trans = v(0) == v(0+2);

    c.learn(inits, bads, trans);
}

void t4()
{
    ctx c(Mode::States);

    /*
    00 - bads
    01 - init
    10 
    11

    trans:
    00<->11
    01<->10
    */
    
    Bf_ptr inits = ~v(0) &  v(1), //01
           bads  = ~v(0) & ~v(1), //00
           trans = (v(0) != v(0+2)) &
                   (v(1) != v(1+2));

    //c.learn(inits, bads, trans);

    /*
    00 - init
    01 - bads
    10 
    11

    trans:
    00<->11
    01<->10
    */
    
    inits = ~v(0) & ~v(1), //00
    bads  = ~v(0) &  v(1), //01
    trans = (v(0) != v(0+2)) &
            (v(1) != v(1+2));

    c.learn(inits, bads, trans);
}

void t5()
{
    Ctx<3> c(Mode::States);

    /*
    000-
    001- bads
    010
    011
    trans: totally connected component
    ---
    trans: totally connected component
    100
    101
    110-
    111- inits
    */
    
    Bf_ptr inits = v(0) &  v(1),
           bads = ~v(0) & ~v(1),
           trans = ( v(0) &  v(0+3)) |
                   (~v(0) & ~v(0+3));

    c.learn(inits, bads, trans);
}

void t6()
{
    Ctx<3> c(Mode::States);

    /*
    000- bad
    001- init
    010
    011
    100
    101
    110
    111
    trans: 7=>0=>1=>2=>3=>1, 4=>5=>6=>4
    */
    
    Bf_ptr inits = characteristic("001");
    Bf_ptr bads = characteristic("000");
    Bf_ptr trans = (~characteristic("011") & ~characteristic("110") |= counter(3)) &
                    (characteristic("011") |= characteristic("001",3)) &
                    (characteristic("110") |= characteristic("100",3));

    //Var x = c.addBf(trans);
    //c.addClause(mkLit(x));
    //c.tabulate();
    c.learn(inits, bads, trans);
}

void t7()
{
    Ctx<3> c(Mode::States);

    /*
    000- bad
    001- init
    010
    011
    100
    101
    110
    111
    trans: 7=>0=>1=>2=>3=>5, 4=>5=>6=>4
    */
    
    Bf_ptr inits = characteristic("001");
    Bf_ptr bads = characteristic("000");
    Bf_ptr trans = (~characteristic("011") & ~characteristic("110") |= counter(3)) &
                    (characteristic("011") |= characteristic("101",3)) &
                    (characteristic("110") |= characteristic("100",3));

    //Var x = c.addBf(trans);
    //c.addClause(mkLit(x));
    //c.tabulate();
    c.learn(inits, bads, trans);
}

void t8()
{
    Ctx<3> c(Mode::States);

    /*
    000- bad
    001- init
    010
    011
    100- bad
    101
    110
    111
    trans: 7=>0=>1=>2=>3=>5, 4=>5=>6=>4
    */
    
    Bf_ptr inits = characteristic("001");
    Bf_ptr bads = characteristic("000") | characteristic("100");
    Bf_ptr trans = (~characteristic("011") & ~characteristic("110") |= counter(3)) &
                    (characteristic("011") |= characteristic("101",3)) &
                    (characteristic("110") |= characteristic("100",3));

    //Var x = c.addBf(trans);
    //c.addClause(mkLit(x));
    //c.tabulate();
    c.learn(inits, bads, trans);
}

void t9()
{
    Ctx<12> c(Mode::States);

    /*
    0000 0000 0000- bad
    0000 0001 0000- init
    0001 0000 0000- bad
    trans: 0000 1000 0000=>0000 0100 0000
           0000 1111 0000=>0000 0100 0000
    */
    
    Bf_ptr inits = characteristic("0000 0001 0000");
    Bf_ptr bads = characteristic("0000 0000 0000") | characteristic("0001 0000 0000");
    Bf_ptr trans = (~characteristic("0000 1000 0000") & ~characteristic("0000 1111 0000") |= counter(12)) &
                    (characteristic("0000 1000 0000") |= characteristic("0000 0100 0000",12)) &
                    (characteristic("0000 1111 0000") |= characteristic("0000 0100 0000",12));

    //Var x = c.addBf(trans);
    //c.addClause(mkLit(x));
    //c.tabulate();
    c.learn(inits, bads, trans);
}

void t10()
{
    constexpr size_t n = 15;
    Ctx<n> c(Mode::States);

    /*
    0000 0000 0000 0000- bad
    0000 0001 0000 0000- init
    0001 0000 0000 0000- bad
    trans: 0000 1000 0000 0000=>0000 0100 0000 0000
           0000 1111 0000 0000=>0000 0100 0000 0000
    */
    
    Bf_ptr inits =   characteristic("0000 0001 0000 000");
    Bf_ptr bads =    characteristic("0000 0000 0000 000") |
                     characteristic("0001 0000 0000 000");
    Bf_ptr trans = (~characteristic("0000 1000 0000 000") &
                    ~characteristic("0000 1111 0000 000") |= counter(n)) &
                    (characteristic("0000 1000 0000 000") |=
                     characteristic("0000 0100 0000 000",n)) &
                    (characteristic("0000 1111 0000 000") |=
                     characteristic("0000 0100 0000 000",n));

    //Var x = c.addBf(trans);
    //c.addClause(mkLit(x));
    //c.tabulate();
    c.learn(inits, bads, trans);
}

#include <chrono>
#include <typeinfo>
int main()
{
    auto t1 = std::chrono::high_resolution_clock::now();
    t10();
    auto t2 = std::chrono::high_resolution_clock::now();

    auto duration = std::chrono::duration_cast<std::chrono::seconds>( t2 - t1 ).count();

    std::cout << duration;
    /*
    Ctx<2> c(Mode::States);
    Face f1 ("00", {"10"});
    vector<Face> cdnf {f1};

    Var f, fp;
    tie(f, fp) = c.tryCdnf(cdnf);
    //c.addClause(mkLit(f));
    //c.addClause(mkLit(fp));
    //c.tryClause(mkLit(f));
    //c.tryClause(mkLit(fp));
    
    Bf_ptr trans_ = (v(0) == v(2));
    Var trans = c.addBf(trans_);
    //c.addClause(mkLit(trans));

    Var cons = c.addBf( ~(v(f)&v(trans)|=v(fp)) );
    c.addClause(mkLit(cons));

    c.tabulate();
    //cout << c.tryOnce ( ~(v(f)&v(trans)>v(fp)) ) << endl;
    //for (size_t n=0; n<4; n++)
    //cout << (c.s.model[n] == l_True);
    //cout << c.s.solve (mkLit(0), mkLit(1));*/
}