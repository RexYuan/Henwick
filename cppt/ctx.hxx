
#pragma once

#include <bitset>
#include <tuple>
#include <set>
#include <map>
#include <vector>
#include <string>

#include <fstream>
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
    map<Step,Var> states; // stepped states offsets; a step of states is N *contiguous* minisat Vars
    set<Step> released;
    inline Step beginStates () const; // index of active state start
    inline Step endStates () const; // index of active state end
    inline Step nStates () const; // number of active state steps
    inline Step addStates (); // add a step of N vars into s and return this step
    inline Step addStates (Var n); // indicate that starting at n there has been a step added
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
    pair<Var,Var> addCdnfSW (Var sw, const FaceVector& cdnf, Step curr, Step next); // optimized to add both curr and next in same traversal

    // Learning algorithms
    //
    struct CE { Bv v; bool t; };
    static string to_string (const CE& ce);
    CE getCE (bool t, Step curr); // ce oracle for inits and bads violation
    CE getCE (Bf_ptr bads, const FaceVector& faces, Step curr, Step next); // ce oracle for trans violation
    
    struct Problem { Var inits; Var bads; Var trans; Step curr; Step next; };
    Problem inputBf (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_);
    Problem inputBf (Var initsSW, Var badsSW, Var transSW, Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_);
    Problem inputAAG (string filename);
    Problem inputAAG (Var initsSW, Var badsSW, Var transSW, string filename);

    void minputInputAAG (string filename, vector<Var>& input_to_var_map);
    void minputStateAAG (string filename, vector<Var>& input_to_var_map, vector<Var>& aag_to_var_map, Step step1);
    Var minputGetInitsAAG (Var initsSW, Step step1);
    Var minputGetBadsAAG (Var badsSW, string filename, vector<Var>& aag_to_var_map, Step step1);
    Var minputGetTransAAG (Var transSW, string filename, vector<Var>& aag_to_var_map, Step step1, Step step2);

    // Recoverable naive cdnf given eventually consistent oracle:
    bool dlearn (string filename);
    bool dlearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    bool dlearn (Problem P);

    // Mccarthy's forward image overapprox with new cdnf deployment in place of interpolant
    bool mlearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    void walk (Bv& b, const Bv& a, Var hypt, Var trans, Bf_ptr sufftrans, Bf_ptr suffbads, Step curr, Step next, vector<Step> suffSteps);
    Var deployCdnfAtomic (Var sw, Var hypt, Var trans, Bf_ptr sufftrans, Bf_ptr suffbads, Step curr, Step next, vector<Step> suffSteps);
    bool mlearn (string filename);

    // Breath-over-depth expansion cdnf
    bool blearn (string filename);
    bool blearn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    bool blearn (Problem P);
    
    inline bool learn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans) { return blearn(inits, bads, trans); }
    Var fixedSW;
    Var constTrue, constFalse;
    Ctx ()
    {
        constTrue = s.newVar();
        assert ( s.addClause(mkLit(constTrue)) );
        constFalse = s.newVar();
        assert ( s.addClause(~mkLit(constFalse)) );

        fixedSW = constFalse;
        //fixedSW = newSW(); //NOTE: how is it that *THIS* is the bottleneck?
    }
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
#include "input.hxx"

// algorithms
#include "dlearn.hxx"
#include "mlearn.hxx"
#include "blearn.hxx"