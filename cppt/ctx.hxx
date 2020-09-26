
#pragma once

#include <bitset>
#include <set>
#include <vector>
#include <string>

#include <iostream>

#include "minisat.hxx"

#include "bf.hxx"

using namespace Minisat;
using namespace std;

enum class Mode {Vars, States};

template <size_t N>
struct Ctx
{
    struct Face;
    
    using Bv = bitset<N>;
    using BvVector = vector<Bv>;
    using FaceVector = vector<Face>;

    static Bv mkBv (string s);
    static BvVector mkBvs (initializer_list<string> ss);
    static string to_string (const Bv& bs);
    static string to_string (const Face& f);
    static string to_string (const FaceVector& fs);

    set<Var> activeSW;
    set<Var> inactiveSW;
    // new switches default to active
    inline Var newSW () { Var sw=s.newVar(); activeSW.insert(sw); return sw; }
    inline void releaseSW (Var sw) { activeSW.erase(sw); inactiveSW.erase(sw); s.releaseVar(mkLit(sw)); }
    inline void activate (Var sw) { inactiveSW.erase(sw); activeSW.insert(sw); }
    inline void deactivate (Var sw) { activeSW.erase(sw); inactiveSW.insert(sw); }
    
    template <typename... Ts> requires (sizeof...(Ts)<=3) && (same_as<Ts, Lit> && ...)
    inline bool addClauseSW (Var sw, Ts... lits) { return s.addClause(mkLit(sw), lits...); }
    template <typename... Ts> requires (sizeof...(Ts)>3) && (same_as<Ts, Lit> && ...)
    inline bool addClauseSW (Var sw, Ts... lits) { vec<Lit> ps; (ps.push(lits), ...); return addClauseSW(sw, ps); }
    inline bool addClauseSW (Var sw, const vec<Lit>& ps) { vec<Lit> tmp; ps.copyTo(tmp); tmp.push(mkLit(sw)); return s.addClause_(tmp); }
    
    template <typename... Ts> requires (same_as<Ts, Lit> && ...)
    bool solveSW (Ts... lits);
    bool solveSW (const vec<Lit>& ps);
    bool solveAtomicSW (Bf_ptr bf);
    bool solveAtomicSW (Bv bv, Bf_ptr bf, int offset=0); // if bv is in bf
    Var addBfSW (Var sw, const Bf_ptr& bf);
    pair<Var,Var> addCdnfSW (Var sw, const FaceVector& cdnf);

    Mode mode;
    Solver s;

    Ctx (Mode m) : mode {m} { init(); }

    inline void tabulate () { switch (mode) {
        case Mode::Vars:   tabulateVars();   break;
        case Mode::States: tabulateStates(); break; } }
    void tabulateVars ();
    void tabulateStates ();

    inline void init () { switch (mode) {
        case Mode::Vars:   initVars();   break;
        case Mode::States: initStates(); break; } }
    void initVars () // call this first
                  { for (int i=0; i<N; i++) s.newVar(); }
    void initStates () // or call this first
                  { for (int i=0; i<N*2; i++) s.newVar(); }
    
    //void walk (Bv& b, const Bv& towards, Bf_ptr bads, const FaceVector& faces);
    bool learn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    Bv ce;
    bool ce_type;
    void decide_ce (Bf_ptr bads, const FaceVector& faces);
    void update_ce (bool t);

    // clean
    bool mclearnInit (FaceVector& faces, Var inits, Var bads);
    bool mclearnStep (FaceVector& faces, Var inits, Var bads, Var trans);
    bool mclearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    void getSucc();
};

template <size_t N>
struct Ctx<N>::Face
{
    Bv basis;
    BvVector primes;

    Face (Bv b) : basis {b}, primes {BvVector{}} {};
    Face (string bs) : basis {mkBv(bs)}, primes {BvVector{}} {};
    Face (Bv b, initializer_list<Bv> bs) : basis {b}, primes {BvVector(bs)} {};
    Face (string bs, initializer_list<string> bss) : basis {mkBv(bs)}, primes {mkBvs(bss)} {};

    void push (Bv b) { primes.push_back(b); }
    void push (string bs) { primes.push_back(mkBv(bs)); }
    void push_absorption (Bv b)
    {
        for (size_t i=0; i<primes.size();)
        if (((b^basis)&(primes[i]^basis)) == (b^basis))
            primes.erase(primes.begin()+i);
        else i++;

        push(b);
    }
    void push_absorption (string bs) { push_absorption(mkBv(bs)); }

    bool operator() (Bv b)
    {
        for (Bv p : primes)
            if (((b^basis)&(p^basis)) == (p^basis))
                return true;
        return false;
    }
};

template <size_t N>
Var Ctx<N>::addBfSW (Var sw, const Bf_ptr& bf)
{
    switch (bf->t)
    {
    case Conn::Top:
    {
        Var v = s.newVar();
        addClauseSW(sw, mkLit(v));
        return v;
        break;
    }   
    case Conn::Bot:
    {
        Var v = s.newVar();
        addClauseSW(sw, ~mkLit(v));
        return v;
        break;
    }
    case Conn::Base:
        return bf->get_int();
        break;    
    case Conn::Not:
    {
        Var v = s.newVar();
        Var sub_v = addBfSW(sw, bf->get_range()[0]);
        addClauseSW(sw,  mkLit(v),  mkLit(sub_v));
        addClauseSW(sw, ~mkLit(v), ~mkLit(sub_v));
        return v;
        break;
    }
    case Conn::And:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push(mkLit(v));
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBfSW(sw, sub);
            addClauseSW(sw, ~mkLit(v), mkLit(sub_v));
            l.push(~mkLit(sub_v));
        }
        addClauseSW(sw, l);
        return v;
        break;
    }
    case Conn::Or:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push(~mkLit(v));
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBfSW(sw, sub);
            addClauseSW(sw, mkLit(v), ~mkLit(sub_v));
            l.push(mkLit(sub_v));
        }
        addClauseSW(sw, l);
        return v;
        break;
    }
    }
    assert( false );
}

template <size_t N>
pair<Var,Var> Ctx<N>::addCdnfSW (Var sw, const FaceVector& cdnf)
{
    assert( s.nVars() >= N*2 );

    Var r = s.newVar(), rp = s.newVar();

    vec<Lit> rls, rpls;
    rls.push(mkLit(sw)); rpls.push(mkLit(sw));
    rls.push(mkLit(r)); rpls.push(mkLit(rp));
    for (Face dnf : cdnf)
    {
        Var dr = s.newVar(), drp = s.newVar();
        addClauseSW(sw, ~mkLit(r), mkLit(dr)); addClauseSW(sw, ~mkLit(rp), mkLit(drp));
        rls.push(~mkLit(dr)); rpls.push(~mkLit(drp));

        vec<Lit> dls, dpls;
        dls.push(mkLit(sw)); dpls.push(mkLit(sw));
        dls.push(~mkLit(dr)); dpls.push(~mkLit(drp));
        for (Bv term : dnf.primes)
        {
            Var cr = s.newVar(), crp = s.newVar();
            addClauseSW(sw, ~mkLit(cr), mkLit(dr)); addClauseSW(sw, ~mkLit(crp), mkLit(drp));
            dls.push(mkLit(cr)); dpls.push(mkLit(crp));

            vec<Lit> cls, cpls;
            cls.push(mkLit(sw)); cpls.push(mkLit(sw));
            cls.push(mkLit(cr)); cpls.push(mkLit(crp));
            for (int i=0; i<N; i++)
            {
                if (term[i] == true && dnf.basis[i] == false)
                {
                    addClauseSW(sw, ~mkLit(cr), mkLit(i)); addClauseSW(sw, ~mkLit(crp), mkLit(i+N));
                    cls.push(~mkLit(i)); cpls.push(~mkLit(i+N));
                }
                else if (term[i] == false && dnf.basis[i] == true)
                {
                    addClauseSW(sw, ~mkLit(cr), ~mkLit(i)); addClauseSW(sw, ~mkLit(crp), ~mkLit(i+N));
                    cls.push(mkLit(i)); cpls.push(mkLit(i+N));
                }
            }
            addClauseSW(sw, cls); addClauseSW(sw, cpls);
        }
        addClauseSW(sw, dls); addClauseSW(sw, dpls);
    }
    addClauseSW(sw, rls); addClauseSW(sw, rpls);
    return make_pair(r,rp);
}

template <size_t N>
template <typename... Ts> requires (same_as<Ts, Lit> && ...)
bool Ctx<N>::solveSW (Ts... lits)
{
    vec<Lit> ps; (ps.push(lits), ...);
    return solveSW(ps);
}

template <size_t N>
bool Ctx<N>::solveSW (const vec<Lit>& ps)
{
    vec<Lit> tmp; ps.copyTo(tmp);
    for (auto sw :   activeSW) tmp.push(~mkLit(sw));
    for (auto sw : inactiveSW) tmp.push( mkLit(sw));
    return s.solve(tmp);
}

template <size_t N>
bool Ctx<N>::solveAtomicSW (Bf_ptr bf)
{
    Var e = newSW();
    bool ret = solveSW(mkLit(addBfSW(e, bf)));
    releaseSW(e);
    return ret;
}

template <size_t N>
bool Ctx<N>::solveAtomicSW (Bv bv, Bf_ptr bf, int offset) // if bv is in bf
{
    vec<Lit> tmp;
    for (size_t i=0; i<N; i++)
        if (bv[i]) tmp.push( mkLit(i+offset) );
        else tmp.push( ~mkLit(i+offset) );
    Var e = newSW();
    tmp.push(mkLit(addBfSW(e, bf)));
    bool ret = solveSW(tmp);
    releaseSW(e);
    return ret;
}

template <size_t N>
void Ctx<N>::tabulateVars ()
{
    assert( s.nVars() >= N );

    cout << "listing truth table:" << endl;
    vec<Lit> tmp;
    for (int i=0; i<pow(2,N); i++)
    {
        Bv tmp_b (i);
        for (int j=0; j<N; j++)
            if (tmp_b[j]) tmp.push(mkLit(j));
            else tmp.push(~mkLit(j));
        
        cout << to_string(tmp_b) << " " << solveSW(tmp) << endl;
        tmp.clear();
    }
}

template <size_t N>
void Ctx<N>::tabulateStates ()
{
    assert( s.nVars() >= N*2 );

    cout << "listing truth table:" << endl;
    vec<Lit> tmp, tmpp, pre;
    for (int i=0; i<pow(2,N); i++)
    {
        Bv tmp_b (i);
        for (int j=0; j<N; j++)
            if (tmp_b[j]) tmp.push(mkLit(j));
            else tmp.push(~mkLit(j));
        
        tmp.copyTo(pre);
        for (int k=0; k<pow(2,N); k++)
        {
            Bv tmp_bp (k);
            for (int l=0; l<N; l++)
                if (tmp_bp[l]) tmp.push(mkLit(l+N));
                else tmp.push(~mkLit(l+N));
            
            cout << to_string(tmp_b) << " " <<
                    to_string(tmp_bp) << " " <<
                    solveSW(tmp) << endl;
            pre.copyTo(tmp);
        }
        tmp.clear();
    }
}

template <size_t N>
Ctx<N>::Bv Ctx<N>::mkBv (string s)
{
    reverse(s.begin(), s.end());
    return Bv (s);
}

template <size_t N>
Ctx<N>::BvVector Ctx<N>::mkBvs (initializer_list<string> ss)
{
    BvVector bvs {};
    for (string s : ss) bvs.push_back(mkBv(s));
    return bvs;
}

template <size_t N>
string Ctx<N>::to_string (const Bv& bs)
{
    string s = bs.to_string();
    reverse(s.begin(), s.end());
    return s;
}

template <size_t N>
string Ctx<N>::to_string (const Face& f)
{
    string s = "";
    s += to_string(f.basis) + ", {";
    if (f.primes.size()>0)
        s += to_string(f.primes[0]);
    for (size_t i=1; i<f.primes.size(); i++)
        s += ", " + to_string(f.primes[i]);
    s += "}\n";
    return s;
}

template <size_t N>
string Ctx<N>::to_string (const FaceVector& fs)
{
    string s = "";
    for (auto f : fs)
        s += to_string(f);
    return s;
}