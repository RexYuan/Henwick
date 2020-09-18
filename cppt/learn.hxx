
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
#include <optional>

#include "ctx.hxx"
#include "bf.hxx"

using namespace Minisat;
using namespace std;

template <size_t N>
bool Ctx<N>::learn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    cout << boolalpha;

    Var inits = addBf(inits_),
        bads  = addBf(bads_),
        trans = addBf(trans_);
    
    if (tryOnce ( v(inits)&v(bads) ))
    {
        cout << "degen false" << endl;
        return false;
    }

    FaceVector faces;
    Var hypt, hyptP;
    bool pass = false;
    
    //if (!tryOnce ( ~(v(inits) |= v(true))) &&
    //    !tryOnce ( ~(v(true)  |= ~v(bads))) &&
    //    !tryOnce ( ~(v(true)&v(trans) |= v(true)) ))
    if (!tryOnce( v(bads) ))
    {
        cout << "degen true" << endl;
        return true;
    }
    
    update_ce(false);
    while (!pass)
    {
        //cout << "cet " <<ce_type <<" , " << "ce " << to_string(ce)<<endl;
        if (ce_type) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce) ) f.push_absorption(ce);
        }
        else // negative ce
        {
            if (tryOnce (ce, v(inits)))
            {
                cout << "violated false" << endl;
                return false;
            }
            faces.push_back( Face(ce) );
        }
        //printFaces(faces);

        tie(hypt,hyptP) = tryCdnf(faces);
        
        if (tryOnce ( ~(v(inits) |= v(hypt)) ))
        {
            //cout << "sat 1" <<endl;
            update_ce(true);
            continue;
        }    
        if (tryOnce ( ~(v(hypt) |= ~v(bads)) ))
        {
            //cout << "sat 2" <<endl;
            update_ce(false);
            continue;
        }
        if (tryOnce ( ~(v(hypt)&v(trans) |= v(hyptP)) ))
        {
            //cout << "sat 3" <<endl;
            decide_ce(v(bads), faces);
            continue;
        }
        pass = true;
    }
    
    cout << "passing true" << endl;
    //printFaces(faces);
    return true;
}

template <size_t N>
void Ctx<N>::decide_ce (Bf_ptr bads, FaceVector faces) // determine ce when trans violated
{
    assert( s.okay() );
    string tmp = "";
    for (size_t i = 0; i < N; i++)
    tmp += (s.model[i] == l_True) ? "1" : "0";
    Bv pred = mkBv(tmp);
    tmp = "";
    for (size_t i = N; i < N+N; i++)
    tmp += (s.model[i] == l_True) ? "1" : "0";
    Bv succ = mkBv(tmp);

    if (tryOnce (succ, bads))
    {
        ce_type = false;
        ce = pred;
        return;
    }
    for (auto f : faces)
    if (f.basis == succ)
    {
        ce_type = false;
        ce = pred;
        return;
    }
    ce_type = true;
    ce = succ;
    return;
}

template <size_t N>
void Ctx<N>::update_ce (bool t)
{
    assert( s.okay() );
    string tmp;
    for (size_t i = 0; i < N; i++)
    tmp += (s.model[i] == l_True) ? "1" : "0";
    ce_type = t;
    ce = mkBv(tmp);
    return;
}