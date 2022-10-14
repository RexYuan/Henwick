
#include "minisat.hxx"

#include "bf.hxx"
#include "ctx.hxx"

#include <chrono>
#include <typeinfo>
void timer ()
{
    static auto start = std::chrono::steady_clock::now();
    static auto run = 0;

    if (run & 1)
    {
        cout << endl;
        auto end = std::chrono::steady_clock::now();
        std::chrono::duration<double> elapsed_seconds = end-start;
        std::cout << "elapsed time: " << elapsed_seconds.count() << "s\n";
    }
    else
    {
        std::cout << "timer starting..." << "\n";
        start = std::chrono::steady_clock::now();
    }
    
    run++;
    return;
}

namespace exposer
{
    //using ctx = Ctx<3>;
    //using Bv = ctx::Bv;
    //using Face = ctx::Face;
    //using FaceVector = ctx::FaceVector;
    //
    //auto& mkBv = ctx::mkBv;
    //auto& mkBvs = ctx::mkBvs;
    //auto& to_string = ctx::to_string;
    //auto& printFace = ctx::printFace;
    //auto& printFaces = ctx::printFaces;
}

using namespace exposer;

void t3()
{
    Ctx<2> c;

    // trans: totally connected component
    // 00 - bads
    // 01 -
    // ---
    // 10 -
    // 11 - inits
    
    Bf_ptr inits = v(0),
           bads = ~v(0),
           trans = v(0) == v(0+2);

    assert ( c.learn(inits, bads, trans) );
    //c.learn(inits, bads, trans);
}

void t4()
{
    Ctx<2> c;

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

    cout << c.learn(inits, bads, trans);

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

    //c.learn(inits, bads, trans);
}

void t5()
{
    Ctx<3> c;

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
    Ctx<3> c;

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
    //c.addStates();
    //c.addStates();
    //Var sw = c.newSW();
    //Var x = c.addBfSW(sw, trans);
    //c.addClauseSW(sw, mkLit(x));
    //c.tabulate();
    
    //cout << "vars " << c.s.nVars() << endl;
    //cout << "states " << c.nStates() << endl;
    cout << c.learn(inits, bads, trans) << endl;
    cout << c.learn(inits, bads, trans) << endl;
    //cout << "vars " << c.s.nVars() << endl;
    //cout << "states " << c.nStates() << endl;
}

void t7()
{
    Ctx<3> c;

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
    assert (c.learn(inits, bads, trans));
}

void t8()
{
    Ctx<3> c;

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
    timer();
    assert (!c.dlearn(inits, bads, trans));
    timer();
    
    timer();
    assert (!c.mlearn(inits, bads, trans));
    timer();
}

void t85()
{
    constexpr size_t bits = 8;
    Ctx<bits> c;

    /*
    0000 0000- bad
    0000 0001- init
    0001 0000- bad
    trans: 0000 1000 =>0000 0100
    */
    
    Bf_ptr inits =   characteristic("0000 0001");
    Bf_ptr bads =    characteristic("0000 0000") |
                     characteristic("0001 0000");
    Bf_ptr trans = (~characteristic("0000 1000") |= counter(bits)) &
                    (characteristic("0000 1000") |=
                     characteristic("0000 0100",bits));

    timer();
    cout << c.dlearn(inits, bads, trans) << endl;
    timer();

    timer();
    cout << c.blearn(inits, bads, trans) << endl;
    timer();

    timer();
    cout << c.mlearn(inits, bads, trans) << endl;
    timer();

    
}

void t9()
{
    Ctx<12> c;

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

    timer();
    cout << c.dlearn(inits, bads, trans) << endl;
    timer();

    timer();
    cout << c.blearn(inits, bads, trans) << endl;
    timer();

    timer();
    cout << c.mlearn(inits, bads, trans) << endl;
    timer();
    //cout << c.learn(inits, bads, trans) << endl;
    //cout << c.learn(inits, bads, trans) << endl;
    //cout << c.learn(inits, bads, trans) << endl;
    //cout << c.learn(inits, bads, trans) << endl;
    //cout << c.learn(inits, bads, trans) << endl;
}

void t10()
{
    constexpr size_t n = 16;
    Ctx<n> c;

    /*
    0000 0000 0000 0000- bad
    0000 0001 0000 0000- init
    0001 0000 0000 0000- bad
    trans: 0000 1000 0000 0000=>0000 0100 0000 0000
           0000 1111 0000 0000=>0000 0100 0000 0000
    */
    
    Bf_ptr inits =   characteristic("0000 0001 0000 ****");
    Bf_ptr bads =    characteristic("0000 0000 0000 ****") |
                     characteristic("0001 0000 0000 ****");
    Bf_ptr trans = (~characteristic("0000 1000 0000 0000") &
                    ~characteristic("0000 1111 0000 0000") |= counter(n)) &
                    (characteristic("0000 1000 0000 0000") |=
                     characteristic("0000 0100 0000 0000",n)) &
                    (characteristic("0000 1111 0000 0000") |=
                     characteristic("0000 0100 0000 0000",n));

    //Var x = c.addBf(trans);
    //c.addClause(mkLit(x));
    //c.tabulate();
    
    timer();
    cout << c.dlearn(inits, bads, trans) << endl;
    timer();

    timer();
    cout << c.blearn(inits, bads, trans) << endl;
    timer();

    timer();
    cout << c.mlearn(inits, bads, trans) << endl;
    timer();
}

// TODO: use setDecisionVar
int main()
{
    cout << boolalpha;

    Ctx<5> c5;
    Ctx<16> c16;

    timer();
    cout << c5.dlearn("aags/pdtvisgray0.aag");
    timer();

    timer();
    cout << c5.blearn("aags/pdtvisgray0.aag");
    timer();

    timer();
    cout << c5.mlearn("aags/pdtvisgray0.aag");
    timer();
    return 0;


    //timer();
    //cout << c5.mlearn("aags/pdtvisgray0.aag");
    //cout << c16.dlearn("aags/pdtvisgigamax1.aag");
    //timer();


    //cout << c5.mlearn("aags/pdtvisgray1.aag");

    //return 0;

    
    
    cout << "pdtvisgigamax0\n";
    timer();
    cout << c16.dlearn("aags/pdtvisgigamax0.aag");
    timer();

    timer();
    cout << c16.blearn("aags/pdtvisgigamax0.aag");
    timer();

    timer();
    cout << c16.mlearn("aags/pdtvisgigamax0.aag");
    timer();

    cout << "\npdtvisgigamax1\n";
    timer();
    cout << c16.dlearn("aags/pdtvisgigamax1.aag");
    timer();

    timer();
    cout << c16.blearn("aags/pdtvisgigamax1.aag");
    timer();

    timer();
    cout << c16.mlearn("aags/pdtvisgigamax1.aag");
    timer();

    cout << "\npdtvisgigamax2\n";
    timer();
    cout << c16.dlearn("aags/pdtvisgigamax2.aag");
    timer();

    timer();
    cout << c16.blearn("aags/pdtvisgigamax2.aag");
    timer();

    timer();
    cout << c16.mlearn("aags/pdtvisgigamax2.aag");
    timer();

    cout << "\npdtvisgigamax3\n";
    timer();
    cout << c16.dlearn("aags/pdtvisgigamax3.aag");
    timer();

    timer();
    cout << c16.blearn("aags/pdtvisgigamax3.aag");
    timer();

    timer();
    cout << c16.mlearn("aags/pdtvisgigamax3.aag");
    timer();

    cout << "\npdtvisgigamax4\n";
    timer();
    cout << c16.dlearn("aags/pdtvisgigamax4.aag");
    timer();

    timer();
    cout << c16.blearn("aags/pdtvisgigamax4.aag");
    timer();

    timer();
    cout << c16.mlearn("aags/pdtvisgigamax4.aag");
    timer();

    cout << "\npdtvisgigamax5\n";
    timer();
    cout << c16.dlearn("aags/pdtvisgigamax5.aag");
    timer();

    timer();
    cout << c16.blearn("aags/pdtvisgigamax5.aag");
    timer();

    timer();
    cout << c16.mlearn("aags/pdtvisgigamax5.aag");
    timer();
    
    return 0;

    //Ctx<33> c33;
    //timer();
    //cout << c33.dlearn("aags/pdtvisheap01.aag");    
    //timer();

    Ctx<28> c28;
    timer();
    cout << c28.dlearn("aags/pdtvisminmaxr0.aag");    
    timer();

    return 0;
/*

    timer();
    cout << c.dlearnAAG("aags/pdtvisgigamax0.aag");
    timer();

    timer();
    cout << c.dlearnAAG("aags/pdtvisgigamax1.aag");
    timer();

    timer();
    cout << c.dlearnAAG("aags/pdtvisgigamax2.aag");
    timer();

    timer();
    cout << c.dlearnAAG("aags/pdtvisgigamax3.aag");
    timer();

    timer();
    cout << c.dlearnAAG("aags/pdtvisgigamax4.aag");
    timer();

    timer();
    cout << c.dlearnAAG("aags/pdtvisgigamax5.aag");
    timer();


    return 0;
    
    
    cout << c.dlearnAAG("aags/pdtvisgray0.aag");
    cout << c.dlearnAAG("aags/test.aag");
*/
    
    //pp c;
    //c.addStates();
    //auto one = pp::Face("00", {"01", "10"});
    //auto two = pp::Face("11", {});
    //pp::FaceVector gg = {one, two};
    //auto k = c.addCdnfSW(c.fixedSW, gg);
    //c.addClauseSW(c.fixedSW, mkLit(k));
    //c.tabulate();

    

    //t3();
    //t4();
    //t5();
    //t6();
    //t7();
    //t8();
    //t85();
    //t9();
    //t10();

    /*Bf_ptr inits_ = v(0),
            bads_ = ~v(0),
           trans_ = v(0) == v(0+2);

    Ctx<2> c;
    Ctx<2>::Step curr = c.addStates(),
                 next = c.addStates();

    Var inits = c.addBfSW(c.fixedSW, inits_, curr),
        bads  = c.addBfSW(c.fixedSW, bads_,  curr),
        trans = c.addBfSW(c.fixedSW, trans_, curr, next);
    
    if ( c.solveAtomicSW( v(inits)&v(bads) )) return false;
    if (!c.solveAtomicSW( v(bads) )) return true;
    
    Ctx<2>::FaceVector faces { Ctx<2>::Face( c.getCE(false, curr).v ) };
    Var h, hP;*/

    /*using pp = Ctx<3>;
    pp c;

    pp::FaceVector faces = { pp::Face("000") };
    pp::Step curr = c.addStates();
    pp::Step next = c.addStates();
    Var  h,  hP; Var nh, nhP;
    Var sw = c.newSW();
    tie(nh,nhP) = c.addCdnfSW (sw, faces, curr, next);
    h=nh; hP=nhP;


    Var asdf = c.newSW();
                cout << "this is nh " << endl;
    c.addClauseSW(asdf, mkLit(nh));
    //c.s.addClause(mkLit(nh));
    c.tabulate();
    c.releaseSW(asdf);*/
}