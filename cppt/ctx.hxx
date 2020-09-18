
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
    using FaceVector = vector<Face>;

    static void printFace (Face f)
    {
        cout << to_string(f.basis) << ", {";
        if (f.primes.size()>0)
        {
            cout << to_string(f.primes[0]);
            for (size_t i=1; i<f.primes.size(); i++)
                cout << ", " << to_string(f.primes[i]);
        }
        cout << "}" << endl;
    }
    static void printFaces (FaceVector fs)
    {
        for (auto f : fs)
        {
            printFace(f);
        }
        cout << endl;
    }

    static Bv mkBv (string s);
    static BvVector mkBvs (initializer_list<string> ss);
    static string to_string (Bv bs);

    bool learn (Bf_ptr inits, Bf_ptr bads, Bf_ptr trans);
    Bv ce;
    bool ce_type;
    void decide_ce (Bf_ptr bads, FaceVector faces);
    void update_ce (bool t);

    Mode mode;
    Solver s;
    Var epoch;

    Ctx (Mode m) : mode {m} { init(); initEpoch(); }

    template <typename... Ts> requires (sizeof...(Ts)<=3) && (same_as<Ts, Lit> && ...)
    inline bool _addClause (Ts... lits) { return addClause(lits...); }
    inline bool  addClause (Lit p) { return s.addClause(p); }
    inline bool  addClause (Lit p, Lit q) { return s.addClause(p, q); }
    inline bool  addClause (Lit p, Lit q, Lit r) { return s.addClause(p, q, r); }
    inline bool  addClause_(vec<Lit>& ps) { return s.addClause_(ps); }

    inline void initEpoch () // call this after initVars / initStates
                          { epoch = s.newVar(); }
    inline void forget ()
                       { s.releaseVar(mkLit(epoch)); epoch = s.newVar(); }
    template <typename... Ts> requires (sizeof...(Ts)<=3) && (same_as<Ts, Lit> && ...)
    inline bool _tryClause (Ts... lits) { return tryClause(lits...); }
    inline bool  tryClause (Lit p)
                           { return s.addClause(mkLit(epoch), p); }
    inline bool  tryClause (Lit p, Lit q)
                           { return s.addClause(mkLit(epoch), p, q); }
    inline bool  tryClause (Lit p, Lit q, Lit r)
                           { return s.addClause(mkLit(epoch), p, q, r); }
    inline bool  tryClause_(vec<Lit>& ps)
                           { ps.push(mkLit(epoch)); return addClause_(ps); }
    inline bool trySolve ()
                         { return s.solve(~mkLit(epoch)); }
    inline bool trySolve (Lit p)
                         { return s.solve(~mkLit(epoch), p); }
    inline bool trySolve (Lit p, Lit q)
                         { return s.solve(~mkLit(epoch), p, q); }
    inline bool tryForget (Lit p)
                          { bool tmp = trySolve(p); forget(); return tmp; }
    
    template <typename... Ts> requires (sizeof...(Ts)<=3) && (same_as<Ts, Lit> && ...)
    inline bool _tryOnce (Var e, Ts... lits) { return tryOnce(e, lits...); }
    inline bool  tryOnce (Var e, Lit p)
                         { return s.addClause(mkLit(e), p); }
    inline bool  tryOnce (Var e, Lit p, Lit q)
                         { return s.addClause(mkLit(e), p, q); }
    inline bool  tryOnce (Var e, Lit p, Lit q, Lit r)
                         { return s.addClause(mkLit(e), p, q, r); }
    inline bool  tryOnce_(Var e, vec<Lit>& ps)
                         { ps.push(mkLit(e)); return addClause_(ps); }
    Var handleOnceBf (Var e, Bf_ptr bf);
    bool tryOnce (Bf_ptr bf)
    {
        Var e = s.newVar();
        bool ret = s.solve(~mkLit(epoch),
            ~mkLit(e),mkLit(handleOnceBf(e, bf)));
        s.releaseVar(mkLit(e));
        return ret;
    }
    bool tryOnce (Bv bv, Bf_ptr bf) // if bv in bf
    {
        Var e = s.newVar();
        vec<Lit> l;
        l.push( ~mkLit(epoch) );
        l.push( ~mkLit(e) );
        l.push( mkLit(handleOnceBf(e, bf)) );
        for (size_t i=0; i<N; i++)
            if (bv[i]) l.push( mkLit(i) );
            else l.push( ~mkLit(i) );

        bool ret = s.solve( l );
        s.releaseVar(mkLit(e));
        return ret;
    }

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
    
    template <bool(Ctx<N>::*)(Lit),
              bool(Ctx<N>::*)(Lit,Lit),
              bool(Ctx<N>::*)(Lit,Lit,Lit),
              bool(Ctx<N>::*)(vec<Lit>&)>
    Var handleBf (Bf_ptr bf);
    inline Var addBf (Bf_ptr bf)
                     { return handleBf<&Ctx<N>::_addClause<Lit>,
                                       &Ctx<N>::_addClause<Lit,Lit>,
                                       &Ctx<N>::_addClause<Lit,Lit,Lit>,
                                       &Ctx<N>::addClause_>(bf); }
    inline Var tryBf (Bf_ptr bf)
                     { return handleBf<&Ctx<N>::_tryClause<Lit>,
                                       &Ctx<N>::_tryClause<Lit,Lit>,
                                       &Ctx<N>::_tryClause<Lit,Lit,Lit>,
                                       &Ctx<N>::tryClause_>(bf); }
    
    template <bool(Ctx<N>::*)(Lit),
              bool(Ctx<N>::*)(Lit,Lit),
              bool(Ctx<N>::*)(Lit,Lit,Lit),
              bool(Ctx<N>::*)(vec<Lit>&)>
    pair<Var,Var> handleCdnf (const FaceVector& cdnf);
    inline pair<Var,Var> addCdnf (const FaceVector& cdnf)
                                 { return handleCdnf<&Ctx<N>::_addClause<Lit>,
                                                     &Ctx<N>::_addClause<Lit,Lit>,
                                                     &Ctx<N>::_addClause<Lit,Lit,Lit>,
                                                     &Ctx<N>::addClause_>(cdnf); }
    inline pair<Var,Var> tryCdnf (const FaceVector& cdnf)
                                 { return handleCdnf<&Ctx<N>::_tryClause<Lit>,
                                                     &Ctx<N>::_tryClause<Lit,Lit>,
                                                     &Ctx<N>::_tryClause<Lit,Lit,Lit>,
                                                     &Ctx<N>::tryClause_>(cdnf); }
};

template <size_t N>
template <bool(Ctx<N>::*handle1)(Lit),
          bool(Ctx<N>::*handle2)(Lit,Lit),
          bool(Ctx<N>::*handle3)(Lit,Lit,Lit),
          bool(Ctx<N>::*handlel)(vec<Lit>&)>
Var Ctx<N>::handleBf (Bf_ptr bf)
{
    switch (bf->t)
    {
    case Conn::Top:
    {
        Var v = s.newVar();
        //invoke(handle1, this, mkLit(v));
        (this->*handle1)( mkLit(v) );
        return v;
        break;
    }   
    case Conn::Bot:
    {
        Var v = s.newVar();
        (this->*handle1)( ~mkLit(v) );
        return v;
        break;
    }
    case Conn::Base:
        return bf->get_int();
        break;    
    case Conn::Not:
    {
        Var v = s.newVar();
        Var sub_v = handleBf<handle1,handle2,handle3,handlel>(bf->get_range()[0]);
        (this->*handle2)(  mkLit(v) ,  mkLit(sub_v) );
        (this->*handle2)( ~mkLit(v) , ~mkLit(sub_v) );
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
            sub_v = handleBf<handle1,handle2,handle3,handlel>(sub);
            (this->*handle2)( ~mkLit(v) , mkLit(sub_v) );
            l.push( ~mkLit(sub_v) );
        }
        (this->*handlel)( l );
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
            sub_v = handleBf<handle1,handle2,handle3,handlel>(sub);
            (this->*handle2)( mkLit(v) , ~mkLit(sub_v) );
            l.push( mkLit(sub_v) );
        }
        (this->*handlel)( l );
        return v;
        break;
    }
    }
    assert( false );
}

template <size_t N>
Var Ctx<N>::handleOnceBf (Var e, Bf_ptr bf)
{
    switch (bf->t)
    {
    case Conn::Top:
    {
        Var v = s.newVar();
        //invoke(handle1, this, mkLit(v));
        _tryOnce(e,  mkLit(v) );
        return v;
        break;
    }   
    case Conn::Bot:
    {
        Var v = s.newVar();
        _tryOnce(e, ~mkLit(v) );
        return v;
        break;
    }
    case Conn::Base:
        return bf->get_int();
        break;    
    case Conn::Not:
    {
        Var v = s.newVar();
        Var sub_v = handleOnceBf(e,bf->get_range()[0]);
        _tryOnce(e,  mkLit(v) ,  mkLit(sub_v) );
        _tryOnce(e, ~mkLit(v) , ~mkLit(sub_v) );
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
            sub_v = handleOnceBf(e,sub);
            _tryOnce(e, ~mkLit(v) , mkLit(sub_v) );
            l.push( ~mkLit(sub_v) );
        }
        tryOnce_(e, l );
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
            sub_v = handleOnceBf(e,sub);
            _tryOnce(e, mkLit(v) , ~mkLit(sub_v) );
            l.push( mkLit(sub_v) );
        }
        tryOnce_(e, l );
        return v;
        break;
    }
    }
    assert( false );
}

template <size_t N>
template <bool(Ctx<N>::*handle1)(Lit),
          bool(Ctx<N>::*handle2)(Lit,Lit),
          bool(Ctx<N>::*handle3)(Lit,Lit,Lit),
          bool(Ctx<N>::*handlel)(vec<Lit>&)>
pair<Var,Var> Ctx<N>::handleCdnf (const FaceVector& cdnf)
{
    assert( s.nVars() >= N*2 );

    Var r = s.newVar(),    rp = s.newVar();
    //addClause(mkLit(r)); addClause(mkLit(rp));

    vec<Lit> rls,       rpls;
    rls.push(mkLit(r)); rpls.push(mkLit(rp));
    for (Face dnf : cdnf)
    {
        Var dr = s.newVar(),               drp = s.newVar();
        (this->*handle2)(~mkLit(r), mkLit(dr)); (this->*handle2)(~mkLit(rp), mkLit(drp));
        rls.push(~mkLit(dr));              rpls.push(~mkLit(drp));

        vec<Lit> dls,         dpls;
        dls.push(~mkLit(dr)); dpls.push(~mkLit(drp));
        for (Bv term : dnf.primes)
        {
            Var cr = s.newVar(),                crp = s.newVar();
            (this->*handle2)(~mkLit(cr), mkLit(dr)); (this->*handle2)(~mkLit(crp), mkLit(drp));
            dls.push(mkLit(cr));                dpls.push(mkLit(crp));

            vec<Lit> cls,        cpls;
            cls.push(mkLit(cr)); cpls.push(mkLit(crp));
            for (int i=0; i<N; i++)
            {
                if (term[i] == true && dnf.basis[i] == false)
                {
                    (this->*handle2)(~mkLit(cr), mkLit(i)); (this->*handle2)(~mkLit(crp), mkLit(i+N));
                    cls.push(~mkLit(i));               cpls.push(~mkLit(i+N));
                }
                else if (term[i] == false && dnf.basis[i] == true)
                {
                    (this->*handle2)(~mkLit(cr), ~mkLit(i)); (this->*handle2)(~mkLit(crp), ~mkLit(i+N));
                    cls.push(mkLit(i));                 cpls.push(mkLit(i+N));
                }
            }
            (this->*handlel)(cls); (this->*handlel)(cpls);
        }
        (this->*handlel)(dls); (this->*handlel)(dpls);
    }
    (this->*handlel)(rls); (this->*handlel)(rpls);
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
            if (tmp_b[j]) addClause(mkLit(tmp_v), mkLit(j));
            else addClause(mkLit(tmp_v), ~mkLit(j));
        
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
            if (tmp_b[j]) addClause(mkLit(tmp_v), mkLit(j));
            else addClause(mkLit(tmp_v), ~mkLit(j));
        
        for (int k=0, tmp_vp=s.newVar(); k<pow(2,N); k++, tmp_vp=s.newVar())
        {
            Bv tmp_bp (k);
            for (int l=0; l<N; l++)
                if (tmp_bp[l]) addClause(mkLit(tmp_vp), mkLit(l+N));
                else addClause(mkLit(tmp_vp), ~mkLit(l+N));
            
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
