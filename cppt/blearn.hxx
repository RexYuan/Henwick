
#pragma once

#include "ctx.hxx"
#include "bf.hxx"

/*template <size_t N>
bool Ctx<N>::blearn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Step curr = addStates(); // current
    Step next = addStates(); // next

    Var fixed = newSW();
    Var inits = addBfSW(fixed, inits_),
        bads  = addBfSW(fixed, bads_),
        trans = addBfSW(fixed, trans_);
    
    if (solveAtomicSW ( v(inits)&v(bads) )) // degen false
        return false;

    FaceVector faces;
    Var hypt, hyptP;
    bool pass = false;

    if (!solveAtomicSW( v(bads) )) // degen true
        return true;
    
    CE ce = dgetCE(curr, false);
    Var sw = newSW();
    while (!pass)
    {
        if (ce.t) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce.v) )
            {
                //walk(ce, f.basis, v(bads), faces);
                f.push_absorption(ce.v);
            }
        }
        else // negative ce
        {
            if (solveAtomicSW (curr, ce.v, v(inits))) // the only way to return false once algo starts
                return false;                         // when a decided neg ce is in inits meaning bads is
                                                      // reachable from inits and refutation is possible
            faces.push_back( Face(ce.v) );
        }

        tie(hypt,hyptP) = daddCdnfSW (curr, sw, faces);
        
        if (solveAtomicSW ( ~(v(inits) |= v(hypt)) ))
            ce = dgetCE(curr, true);
        else if (solveAtomicSW ( ~(v(hypt) |= ~v(bads)) ))
            ce = dgetCE(curr, false);
        else if (solveAtomicSW ( ~(v(hypt)&v(trans) |= v(hyptP)) ))
            ce = dgetCE(curr, next, v(bads), faces);
        else
            pass = true;
        
        releaseSW(sw);
        sw = newSW();
    }
    
    releaseSW(fixed);
    releaseSW(sw);
    releaseStates(curr);
    releaseStates(next);

    cout << to_string(faces);
    return true;
}

template <size_t N>
bool Ctx<N>::grow (Var pred, Var inits, Var bads, Var trans, FaceVector& faces, Step next)
{
    Var sw = newSW();
    Var succ  = addCdnfSW (sw, faces, next);
    if (!solveAtomicSW ( ~(v(pred)&v(trans) |= v(succ)) )) // is invariant
        return false;

    bool pass = false;
    CE ce = dgetCE(true, next);

    releaseSW(sw);
    sw = newSW();
    while (!pass)
    {
        cout << to_string(faces) << flush;
        if (ce.t) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce.v) )
                f.push_absorption(ce.v);
        }
        else // negative ce
        {
            faces.push_back( Face(ce.v) );
        }

        succ = addCdnfSW (sw, faces, next);
        
        if (solveAtomicSW ( ~(v(inits) |= v(succ)) ))
            {ce = dgetCE(true, next); cout << "1" << flush;}
        else if (solveAtomicSW ( ~(v(succ) |= ~v(bads)) )) // FIXME: the problem is with different state space between bads and succ
            {ce = dgetCE(false, next); cout << "2" << flush << endl; 
            cout << to_string(ce.v) << endl;
            return true;}
        else if (solveAtomicSW ( ~(v(pred)&v(trans) |= v(succ)) ))
            {ce = dgetCE(true, next); cout << "3" << flush;}
        else
            pass = true;
        
        releaseSW(sw);
        sw = newSW();
    }
    releaseSW(sw);

    return true;
}*/