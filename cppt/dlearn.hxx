
#pragma once

#include "ctx.hxx"
#include "bf.hxx"

template <size_t N>
bool Ctx<N>::dlearn (string filename)
{
    Problem P = inputAAG (filename);
    return dlearn (P);
}

template <size_t N>
bool Ctx<N>::dlearn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Problem P = inputBf (inits_, bads_, trans_);
    return dlearn (P);
}

template <size_t N>
bool Ctx<N>::dlearn (Problem P)
{
    Var inits = P.inits,
        bads  = P.bads, 
        trans = P.trans; 
    Step curr = P.curr,
         next = P.next;

    if (solveAtomicSW ( v(inits)&v(bads) )) // degen false
        return false;

    FaceVector faces;
    Var hypt, hyptP;
    bool pass = false;

    if (!solveAtomicSW( v(bads) )) // degen true
        return true;

    CE ce = getCE(false, curr);
    Var sw = newSW();
    while (!pass)
    {
        if (ce.t) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce.v) )
                f.push_absorption(ce.v);
        }
        else // negative ce
        {
            if ( evalAtomicSW (ce.v, v(inits), curr) ) // the only way to return false once algo starts
                return false;                          // when a decided neg ce is in inits meaning bads is
                                                       // reachable from inits and refutation is possible
            faces.push_back( Face(ce.v) );
        }

        // equivalent to:
        // hypt  = addCdnfSW (sw, faces, curr);
        // hyptP = addCdnfSW (sw, faces, next);
        tie(hypt,hyptP) = addCdnfSW (sw, faces, curr, next);
        
        if (solveAtomicSW ( ~(v(inits) |= v(hypt)) ))
            ce = getCE(true, curr);
        else if (solveAtomicSW ( ~(v(hypt) |= ~v(bads)) ))
            ce = getCE(false, curr);
        else if (solveAtomicSW ( ~(v(hypt)&v(trans) |= v(hyptP)) ))
            ce = getCE(v(bads), faces, curr, next);
        else
            pass = true;
        
        releaseSW(sw);
        sw = newSW();
    }

    releaseSW(sw);
    releaseStates(curr);
    releaseStates(next);

    //cout << to_string(faces);
    return true;
}

template <size_t N>
Ctx<N>::CE Ctx<N>::getCE (bool t, Step curr)
{
    assert( s.okay() );

    string tmp;
    for (Var i=states[curr], h=i+N; i<h; i++)
        tmp += (s.model[i] == l_True) ? "1" : "0";

    return CE {mkBv(tmp), t};
}

template <size_t N>
Ctx<N>::CE Ctx<N>::getCE (Bf_ptr bads, const FaceVector& faces, Step curr, Step next)
{
    assert( s.okay() );
    
    string tmp = "";
    for (Var i=states[curr], h=i+N; i<h; i++)
        tmp += (s.model[i] == l_True) ? "1" : "0";
    Bv pred = mkBv(tmp);
    
    tmp = "";
    for (Var i=states[next], h=i+N; i<h; i++)
        tmp += (s.model[i] == l_True) ? "1" : "0";
    Bv succ = mkBv(tmp);

    // if succ is in bads => pred is false
    if (evalAtomicSW (succ, bads, curr))
        return CE {pred, false};
    // if succ is an old neg ce => pred is false
    for (const auto& f : faces)
    if (f.basis == succ)
        return CE {pred, false};
    // else => succ is true
    return CE {succ, true};
}