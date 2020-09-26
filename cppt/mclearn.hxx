

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
bool Ctx<N>::mclearnInit (FaceVector& faces, Var inits, Var bads)
{
    /*
    learn overapprox of inits and underapprox of bads:
        init => hypothesis
        hypothesis => ~bads
    */
    if (!tryOnce( v(bads) )) return true; // degen true
    
    bool pass = false;
    Var hypt, hyptP;

    update_ce(false); // neg ce
    while (!pass)
    {
        forget();

        if (ce_type) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce) )
            {
                //walk(ce, f.basis, v(bads), faces);
                f.push_absorption(ce);
            }
        }
        else // negative ce
        {
            if (tryOnce (ce, v(inits))) return false;
            faces.push_back( Face(ce) );
        }

        tie(hypt,hyptP) = tryCdnf(faces);
        
        if (tryOnce ( ~(v(inits) |= v(hypt)) ))
            update_ce(true);
        else if (tryOnce ( ~(v(hypt) |= ~v(bads)) ))
            update_ce(false);
        else
            pass = true;
    }
    forget();
    return false;
}

template <size_t N>
bool Ctx<N>::mclearnStep (FaceVector& faces, Var inits, Var bads, Var trans)
{
    /*
    learn overapprox of hypothesis and a step after and underapprox of bads:
        init => hypothesis
        hypothesis => ~bads
        hypothesis & trans => hypothesis next
    */
    Var hypt, hyptP, oldhypt, oldhyptP; Var sw = newSW();
    tie(oldhypt,oldhyptP) = addCdnfSW (sw, faces);
    if (tryOnce ( ~(v(oldhypt)&v(trans) |= v(oldhyptP)) )) return true; // inv found
    
    bool pass = false;
    getSucc(); // successor as pos ce
    while (!pass)
    {
        forget();

        if (ce_type) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce) )
            {
                //walk(ce, f.basis, v(bads), faces);
                f.push_absorption(ce);
            }
        }
        else // negative ce not possible
        {
            assert( false );
        }

        tie(hypt,hyptP) = tryCdnf(faces);
        
        if (tryOnce ( ~(v(inits) |= v(hypt)) ))
            update_ce(true);
        else if (tryOnce ( ~(v(hypt) |= ~v(bads)) ))
            update_ce(false);
        else if (tryOnce ( ~(v(hypt)&v(trans) |= v(hyptP)) ))
            getSucc();
        else
            pass = true;
    }
    return false;
}

template <size_t N>
bool Ctx<N>::mclearn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Var inits = addBf(inits_),
        bads  = addBf(bads_),
        trans = addBf(trans_);
    
    if (tryOnce ( v(inits)&v(bads) ))
        return false; // invariant not possible

    FaceVector faces;
    if (mclearnInit (faces, inits, bads))
        return true; // invariant already found. its "True"

    while (!mclearnStep (faces, inits, bads, trans))
    {
        // extends reachable to bads
        
    }
    
    cout << "passing true" << endl;
    printFaces(faces);
    return true;
}

template <size_t N>
void Ctx<N>::getSucc()
{
    assert( s.okay() );
    string tmp = "";
    for (size_t i = N; i < N+N; i++)
    tmp += (s.model[i] == l_True) ? "1" : "0";
    ce = mkBv(tmp);
    ce_type = true;
    return;
}