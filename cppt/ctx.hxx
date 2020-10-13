
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
    set<Step> released;
    inline Step beginStates () const; // index of active state start
    inline Step endStates () const; // index of active state end
    inline Step nStates () const; // number of active state steps
    inline Step addStates (); // add a step of N vars into s and return this step
    inline void releaseStates (Step step);
    Bf_ptr substitute (Bf_ptr bf, Step from, Step to); // transform statespace
    
    void tabulate (); // tabulate current truth table considering every state's values
    void tabulate (Step step); // tabulate current truth table considering only given step's valuation

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
    bool evalAtomicSW (const Bv& bv, const Bf_ptr& bf, optional<Step> step=nullopt); // if bv is in bf
    Var addBfSW (Var sw, const Bf_ptr& bf, optional<Step> step1=nullopt, optional<Step> step2=nullopt);
    Var addCdnfSW (Var sw, const FaceVector& cdnf, optional<Step> step=nullopt);

    // Learning algorithms
    //
    struct CE { Bv v; bool t; };
    static string to_string (const CE& ce);
    // Recoverable cdnf given eventually consistent oracle:
    /*void walk (Bv& b, const Bv& towards, Bf_ptr bads, const FaceVector& faces);*/
    CE dgetCE (bool t, Step curr); // ce oracle for inits and bads violation
    CE dgetCE (Bf_ptr bads, const FaceVector& faces, Step curr, Step next); // ce oracle for trans violation
    pair<Var,Var> addCdnfSW (Var sw, const FaceVector& cdnf, Step curr, Step next); // optimized to add both curr and next in same traversal
    bool dlearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);

    Var deployCdnfAtomic (Var sw, Var hypt, Var trans, Bf_ptr sufftrans, Bf_ptr suffbads, Step curr, Step next);
    bool mlearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);

    // Breath-over-depth expansion cdnf
    // TODO: clean and rewrite
    bool blearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    bool grow (Var pred, Var inits, Var bads, Var trans, FaceVector& faces, Step next); // returns true if progress was made
    

    inline bool learn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans) { return mlearn(inits, bads, trans); }
    Ctx () {}
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

// helpers
#include "misc.hxx"
#include "state.hxx"
#include "switch.hxx"

// algorithms
#include "dlearn.hxx"
#include "mlearn.hxx"
#include "blearn.hxx"