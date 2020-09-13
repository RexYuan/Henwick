
#pragma once

#include <iostream>
#include <algorithm>
#include <bitset>
#include <functional>
#include <vector>
#include <variant>
#include <memory>
#include <string>
#include <utility>

#include "minisat.hxx"

#include "bf.hxx"

using namespace Minisat;
using namespace std;

enum class Mode {Vars, States};

template <size_t N>
struct Ctx
{
    using Bv = bitset<N>;
    using BvVector = vector<Bv>;

    struct Face
    {
        Bv basis;
        BvVector primes;

        Face (Bv b) : basis {b}, primes {BvVector{}} {};
        Face (string bs) : basis {mkBv(bs)}, primes {BvVector{}} {};
        Face (Bv b, initializer_list<Bv> bs) : basis {b}, primes {BvVector(bs)} {};
        Face (string bs, initializer_list<string> bss) : basis {mkBv(bs)}, primes {mkBvs(bss)} {};

        void push (Bv b) { primes.push_back(b); }
        void push (string bs) { primes.push_back(mkBv(bs)); }
    };

    static Bv mkBv (string s);
    static BvVector mkBvs (initializer_list<string> ss);
    static string to_string (Bv bs);

    Mode mode;
    Solver s;
    int epoch;

    Ctx (Mode m) : mode {m} { init(); initEpoch(); }

    inline void initEpoch () // call this after initVars / initStates
                          { epoch = s.newVar(); }
    inline void forget ()
                       { s.releaseVar(mkLit(epoch)); epoch = s.newVar(); }
    inline bool tryClause (Lit p)
                          { return s.addClause(mkLit(epoch), p); }
    inline bool tryClause (Lit p, Lit q)
                          { return s.addClause(mkLit(epoch), p, q); }
    inline bool tryClause (Lit p, Lit q, Lit r)
                          { return s.addClause(mkLit(epoch), p, q, r); }
    inline bool tryClause_(vec<Lit>& ps)
                          { ps.push(mkLit(epoch)); return s.addClause_(ps); }
    inline bool tryVar (Var v)
                       { return s.solve(~mkLit(epoch), mkLit(v)); }
    inline bool trySolve ()
                         { return s.solve(~mkLit(epoch)); }
    inline bool trySolve (Lit p)
                         { return s.solve(~mkLit(epoch), p); }
    inline bool trySolve (Lit p, Lit q)
                         { return s.solve(~mkLit(epoch), p, q); }

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
    
    Var addBf (Bf_ptr bf);
    Var tryBf (Bf_ptr bf);
    
    pair<Var,Var> addCdnf (const vector<Face>& cdnf);
    pair<Var,Var> tryCdnf (const vector<Face>& cdnf);
};

template <size_t N>
Var Ctx<N>::addBf (Bf_ptr bf)
{
    switch (bf->t)
    {
    case Conn::Top:
    {
        Var v = s.newVar();
        s.addClause( mkLit(v) );
        return v;
        break;
    }   
    case Conn::Bot:
    {
        Var v = s.newVar();
        s.addClause( ~mkLit(v) );
        return v;
        break;
    }
    case Conn::Base:
        return bf->get_int();
        break;    
    case Conn::Not:
    {
        Var v = s.newVar();
        Var sub_v = addBf(bf->get_range()[0]);
        s.addClause(  mkLit(v) ,  mkLit(sub_v) );
        s.addClause( ~mkLit(v) , ~mkLit(sub_v) );
        return v;
        break;
    }
    case Conn::And:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push( mkLit(v) );
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBf(sub);
            s.addClause( ~mkLit(v) , mkLit(sub_v) );
            l.push( ~mkLit(sub_v) );
        }
        s.addClause_( l );
        return v;
        break;
    }
    case Conn::Or:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push( ~mkLit(v) );
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBf(sub);
            s.addClause( mkLit(v) , ~mkLit(sub_v) );
            l.push( mkLit(sub_v) );
        }
        s.addClause_( l );
        return v;
        break;
    }
    }
    assert( false );
}

template <size_t N>
Var Ctx<N>::tryBf (Bf_ptr bf)
{
    switch (bf->t)
    {
    case Conn::Top:
    {
        Var v = s.newVar();
        tryClause( mkLit(v) );
        return v;
        break;
    }   
    case Conn::Bot:
    {
        Var v = s.newVar();
        tryClause( ~mkLit(v) );
        return v;
        break;
    }
    case Conn::Base:
        return bf->get_int();
        break;    
    case Conn::Not:
    {
        Var v = s.newVar();
        Var sub_v = addBf(bf->get_range()[0]);
        tryClause(  mkLit(v) ,  mkLit(sub_v) );
        tryClause( ~mkLit(v) , ~mkLit(sub_v) );
        return v;
        break;
    }
    case Conn::And:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push( mkLit(v) );
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBf(sub);
            tryClause( ~mkLit(v) , mkLit(sub_v) );
            l.push( ~mkLit(sub_v) );
        }
        tryClause_( l );
        return v;
        break;
    }
    case Conn::Or:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push( ~mkLit(v) );
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBf(sub);
            tryClause( mkLit(v) , ~mkLit(sub_v) );
            l.push( mkLit(sub_v) );
        }
        tryClause_( l );
        return v;
        break;
    }
    }
    assert( false );
}

template <size_t N>
pair<Var,Var> Ctx<N>::addCdnf (const vector<Face>& cdnf)
{
    assert( s.nVars() >= N*2 );

    Var r = s.newVar(),    rp = s.newVar();
    //s.addClause(mkLit(r)); s.addClause(mkLit(rp));

    vec<Lit> rls,       rpls;
    rls.push(mkLit(r)); rpls.push(mkLit(rp));
    for (Face dnf : cdnf)
    {
        Var dr = s.newVar(),               drp = s.newVar();
        s.addClause(~mkLit(r), mkLit(dr)); s.addClause(~mkLit(rp), mkLit(drp));
        rls.push(~mkLit(dr));              rpls.push(~mkLit(drp));

        vec<Lit> dls,         dpls;
        dls.push(~mkLit(dr)); dpls.push(~mkLit(drp));
        for (Bv term : dnf.primes)
        {
            Var cr = s.newVar(),                crp = s.newVar();
            s.addClause(~mkLit(cr), mkLit(dr)); s.addClause(~mkLit(crp), mkLit(drp));
            dls.push(mkLit(cr));                dpls.push(mkLit(crp));

            vec<Lit> cls,        cpls;
            cls.push(mkLit(cr)); cpls.push(mkLit(crp));
            for (int i=0; i<N; i++)
            {
                if (term[i] == true && dnf.basis[i] == false)
                {
                    s.addClause(~mkLit(cr), mkLit(i)); s.addClause(~mkLit(crp), mkLit(i+N));
                    cls.push(~mkLit(i));               cpls.push(~mkLit(i+N));
                }
                else if (term[i] == false && dnf.basis[i] == true)
                {
                    s.addClause(~mkLit(cr), ~mkLit(i)); s.addClause(~mkLit(crp), ~mkLit(i+N));
                    cls.push(mkLit(i));                 cpls.push(mkLit(i+N));
                }
            }
            s.addClause_(cls); s.addClause_(cpls);
        }
        s.addClause_(dls); s.addClause_(dpls);
    }
    s.addClause_(rls); s.addClause_(rpls);
    return make_pair(r,rp);
}

template <size_t N>
pair<Var,Var> Ctx<N>::tryCdnf (const vector<Face>& cdnf)
{
    assert( s.nVars() >= N*2 );

    Var r = s.newVar(),    rp = s.newVar();
    //tryClause(mkLit(r)); tryClause(mkLit(rp));

    vec<Lit> rls,       rpls;
    rls.push(mkLit(r)); rpls.push(mkLit(rp));
    for (Face dnf : cdnf)
    {
        Var dr = s.newVar(),               drp = s.newVar();
        tryClause(~mkLit(r), mkLit(dr));   tryClause(~mkLit(rp), mkLit(drp));
        rls.push(~mkLit(dr));              rpls.push(~mkLit(drp));

        vec<Lit> dls,         dpls;
        dls.push(~mkLit(dr)); dpls.push(~mkLit(drp));
        for (Bv term : dnf.primes)
        {
            Var cr = s.newVar(),                crp = s.newVar();
            tryClause(~mkLit(cr), mkLit(dr));   tryClause(~mkLit(crp), mkLit(drp));
            dls.push(mkLit(cr));                dpls.push(mkLit(crp));

            vec<Lit> cls,        cpls;
            cls.push(mkLit(cr)); cpls.push(mkLit(crp));
            for (int i=0; i<N; i++)
            {
                if (term[i] == true && dnf.basis[i] == false)
                {
                    tryClause(~mkLit(cr), mkLit(i));   tryClause(~mkLit(crp), mkLit(i+N));
                    cls.push(~mkLit(i));               cpls.push(~mkLit(i+N));
                }
                else if (term[i] == false && dnf.basis[i] == true)
                {
                    tryClause(~mkLit(cr), ~mkLit(i));   tryClause(~mkLit(crp), ~mkLit(i+N));
                    cls.push(mkLit(i));                 cpls.push(mkLit(i+N));
                }
            }
            tryClause_(cls); tryClause_(cpls);
        }
        tryClause_(dls); tryClause_(dpls);
    }
    tryClause_(rls); tryClause_(rpls);
    return make_pair(r,rp);
}

template <size_t N>
void Ctx<N>::tabulateVars ()
{
    assert( s.nVars() >= N );

    cout << "listing truth table:" << endl;
    for (int i=0, tmp_v=s.newVar(); i<pow(2,N); i++, tmp_v=s.newVar())
    {
        Bv tmp_b (i);
        for (int j=0; j<N; j++)
            if (tmp_b[j]) s.addClause(mkLit(tmp_v), mkLit(j));
            else s.addClause(mkLit(tmp_v), ~mkLit(j));
        
        cout << to_string(tmp_b) << " " << trySolve(~mkLit(tmp_v)) << endl;
        s.releaseVar(mkLit(tmp_v));
    }
}

template <size_t N>
void Ctx<N>::tabulateStates ()
{
    assert( s.nVars() >= N*2 );

    cout << "listing truth table:" << endl;
    for (int i=0, tmp_v=s.newVar(); i<pow(2,N); i++, tmp_v=s.newVar())
    {
        Bv tmp_b (i);
        for (int j=0; j<N; j++)
            if (tmp_b[j]) s.addClause(mkLit(tmp_v), mkLit(j));
            else s.addClause(mkLit(tmp_v), ~mkLit(j));
        
        for (int k=0, tmp_vp=s.newVar(); k<pow(2,N); k++, tmp_vp=s.newVar())
        {
            Bv tmp_bp (k);
            for (int l=0; l<N; l++)
                if (tmp_bp[l]) s.addClause(mkLit(tmp_vp), mkLit(l+N));
                else s.addClause(mkLit(tmp_vp), ~mkLit(l+N));
            
            cout << to_string(tmp_b) << " " <<
                    to_string(tmp_bp) << " " <<
                    trySolve(~mkLit(tmp_v),~mkLit(tmp_vp)) << endl;
            s.releaseVar(mkLit(tmp_vp));
        }
        s.releaseVar(mkLit(tmp_v));
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
string Ctx<N>::to_string (Ctx<N>::Bv bs)
{
    string s = bs.to_string();
    reverse(s.begin(), s.end());
    return s;
}