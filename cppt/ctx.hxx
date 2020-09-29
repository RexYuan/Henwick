
#pragma once

#include <bitset>
#include <set>
#include <map>
#include <vector>
#include <string>

#include <iostream>
#include <functional>

#include "minisat.hxx"

#include "bf.hxx"

using namespace Minisat;
using namespace std;

template <size_t N>
struct Ctx
{
    Solver s; // context-wise global solver

    struct Face; // dnf representation
    
    using Bv = bitset<N>;
    using BvVector = vector<Bv>;
    using FaceVector = vector<Face>;

    static Bv mkBv (string s);
    static BvVector mkBvs (initializer_list<string> ss);
    static string to_string (const Bv& bs);
    static string to_string (const Face& f);
    static string to_string (const FaceVector& fs);

    // State management
    //
    using Step = size_t;
    map<Step,Var> states; // stepped states offsets
    inline Step nStates () const { return states.size(); } // number of active state steps
    inline Step addStates () { states[nStates()]=s.nVars(); for (size_t i=0; i<N; i++) s.newVar(); return nStates()-1; } // add a step of N vars into s and return this step
    inline void releaseStates (Step step) { for (Var i=states[step], h=i+N; i<h; i++) s.releaseVar(mkLit(i)); states.erase(step); }
    
    void tabulate (); // tabulate current truth table considering every state's values
    void tabulate (int step); // tabulate current truth table considering only given step's valuation

    Ctx () {}
    Ctx (int steps) { for (size_t i=0; i<steps; i++) addStates(); }

    // Switch management
    //
    set<Var> activeSW;
    set<Var> inactiveSW;
    
    Var newSW (); // new switches default to active
    void releaseSW (Var sw);
    void activate (Var sw);
    void deactivate (Var sw);
    
    template <typename... Ts> requires (sizeof...(Ts)<=3) && (same_as<Ts, Lit> && ...)
    bool addClauseSW (Var sw, Ts... lits);
    template <typename... Ts> requires (sizeof...(Ts)>3) && (same_as<Ts, Lit> && ...)
    bool addClauseSW (Var sw, Ts... lits);
    bool addClauseSW (Var sw, const vec<Lit>& ps);
    
    template <typename... Ts> requires (same_as<Ts, Lit> && ...)
    bool solveSW (Ts... lits);
    bool solveSW (const vec<Lit>& ps);
    bool solveAtomicSW (const Bf_ptr& bf);
    bool solveAtomicSW (Step step, const Bv& bv, const Bf_ptr& bf); // if bv is in bf
    Var addBfSW (Var sw, const Bf_ptr& bf);
    pair<Var,Var> addCdnfSW (Step step, Var sw, const FaceVector& cdnf);

    struct CE { Bv v; bool t; };
    // Recoverable cdnf given eventually consistent oracle:
    //
    /*void walk (Bv& b, const Bv& towards, Bf_ptr bads, const FaceVector& faces);*/
    CE dgetCE (Step curr, bool t); // ce oracle for inits and bads violation
    CE dgetCE (Step curr, Step next, Bf_ptr bads, const FaceVector& faces); // ce oracle for trans violation
    pair<Var,Var> daddCdnfSW (Step curr, Var sw, const FaceVector& cdnf); // optimized to add both curr and next in same traversal
    bool dlearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);

    // Breath-over-depth expansion cdnf
    // TODO: clean and rewrite
    bool mclearnInit (FaceVector& faces, Var inits, Var bads);
    bool mclearnStep (FaceVector& faces, Var inits, Var bads, Var trans);
    bool mclearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    void getSucc();

    inline bool learn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans) { return dlearn(inits, bads, trans); }
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
        for (auto p_it=primes.begin(); p_it!=primes.end();)
        if ( ((b^basis)&(*p_it^basis))==(b^basis) )
            primes.erase(p_it);
        else p_it++;

        push(b);
    }
    void push_absorption (string bs) { push_absorption(mkBv(bs)); }

    bool operator() (const Bv& b)
    {
        for (Bv p : primes)
            if ( ((b^basis)&(p^basis))==(p^basis) )
                return true;
        return false;
    }
};

template <size_t N>
void Ctx<N>::tabulate ()
{
    assert( nStates() > 0 );
    cout << "listing truth table:" << endl;
    
    auto to_bs = [&](int i) -> string
    {
        string s;
        for (int j=0; j<N; j++, i>>=1)
            if (1&i) s = "1"+s;
            else s = "0"+s;
        return s;
    };
    auto baseHelper = [&](string bss) -> void
    {
        vec<Lit> tmp;
        for (Step s=0, nS=nStates(); s<nS; s++)
        for (Var b=0; b<N; b++)
            if (bss[N*s+b]=='1') tmp.push(mkLit(b+states[s]));
            else tmp.push(~mkLit(b+states[s]));

        for (Step s=0, nS=nStates(); s<nS; s++) bss.insert(N*s+s, " ");
        cout << bss << " " << solveSW(tmp) << endl;
    };
    function<void(string,unsigned int)> recurHelper;
    recurHelper = [&to_bs,&baseHelper,&recurHelper](string prefix, unsigned int depth) -> void
    {
        if (depth == 0)
            baseHelper(prefix);
        else
            for (unsigned int i=0; i<pow(2,N); i++)
                recurHelper(prefix+to_bs(i), depth-1);
    };

    recurHelper("", nStates());
}

template <size_t N>
void Ctx<N>::tabulate (int step)
{
    assert( nStates() > step );
    cout << "listing truth table of step " << step << ":" << endl;
    vec<Lit> tmp;
    for (int i=0, offset=states[step]; i<pow(2,N); i++)
    {
        Bv tmp_b (i);
        for (int j=0; j<N; j++)
            if (tmp_b[j]) tmp.push(mkLit(j+offset));
            else tmp.push(~mkLit(j+offset));
        
        cout << to_string(tmp_b) << " " << solveSW(tmp) << endl;
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

#include "sw.hxx"
#include "dlearn.hxx"
#include "blearn.hxx"