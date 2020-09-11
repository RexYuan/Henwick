
#pragma once

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

using namespace Minisat;
using namespace std;

template <size_t N>
struct Ctx
{
    using Bv = bitset<N>;

    struct Face
    {
        Bv basis;
        vector<Bv> primes;

        Face (Bv b) : basis {b}, primes {vector<Bv>{}} {};
        Face (string bs) : basis {mkBv(bs)}, primes {vector<Bv>{}} {};
        Face (Bv b, initializer_list<Bv> bs) : basis {b}, primes {vector<Bv>(bs)} {};
        Face (string bs, initializer_list<string> bss) : basis {mkBv(bs)}, primes {mkBvs(bss)} {};

        void push (Bv b) { primes.push_back(b); }
        void push (string bs) { primes.push_back(mkBv(bs)); }
    };

    static Bv mkBv (string s)
    {
        reverse(s.begin(), s.end());
        return Bv (s);
    }
    static vector<Bv> mkBvs (initializer_list<string> ss)
    {
        vector<Bv> bvs {};
        for (string s : ss) bvs.push_back(mkBv(s));
        return bvs;
    }
    static string to_string (bitset<N> bs)
    {
        string s = bs.to_string();
        reverse(s.begin(), s.end());
        return s;
    }

    Solver s;

    Ctx () {};

    void printStates ()
    {
        assert( s.nVars() >= N*2 );

        cout << "current states: ";
        for (int i=0; i<N; i++)
        if (s.value(i) == l_True)
            cout << '1';
        else if (s.value(i) == l_False)
            cout << '0';
        else
            cout << '?';
        cout<<endl;

        cout << "next states: ";
        for (int i=N; i<N+N; i++)
        if (s.value(i) == l_True)
            cout << '1';
        else if (s.value(i) == l_False)
            cout << '0';
        else
            cout << '?';
        cout<<endl;
    }

    void tabulate ()
    {
        assert( s.nVars() >= N );

        cout << "listing truth table:" << endl;
        for (int i=0, tmp_v=s.newVar(); i<pow(2,N); i++, tmp_v=s.newVar())
        {
            Bv tmp_b (i);
            for (int j=0; j<N; j++)
                if (tmp_b[j]) s.addClause(mkLit(tmp_v), mkLit(j));
                else s.addClause(mkLit(tmp_v), ~mkLit(j));
            
            cout << to_string(tmp_b) << " " << s.solve(~mkLit(tmp_v)) << endl;
            s.releaseVar(mkLit(tmp_v));
        }
    }

    void init_cdnf ()
    {
        for (int i=0; i<N*2; i++) s.newVar();
    }

    void add_cdnf (const vector<Face>& cdnf)
    {
        assert( s.nVars() >= N*2 );

        Var r = s.newVar(),    rp = s.newVar();
        s.addClause(mkLit(r)); s.addClause(mkLit(rp));

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
    }
};