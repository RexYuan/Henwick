
#pragma once

#include "ctx.hxx"
#include "bf.hxx"

template <size_t N>
bool Ctx<N>::blearn (string filename)
{
    Problem P = inputAAG (filename);
    return blearn (P);
}

template <size_t N>
bool Ctx<N>::blearn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Problem P = inputBf (inits_, bads_, trans_);
    return blearn (P);
}

template <size_t N>
bool Ctx<N>::blearn (Problem P)
{
    Var inits = P.inits,
        bads  = P.bads, 
        trans = P.trans; 
    Step curr = P.curr,
         next = P.next;
    
    if ( solveAtomicSW( v(inits)&v(bads) )) return false;
    if (!solveAtomicSW( v(bads) )) return true;
    
    FaceVector faces = { Face(getCE(false, curr).v) };
    Var  h,  hP; Var nh, nhP;
    Var sw = newSW(), nsw = newSW();
    tie(nh,nhP) = addCdnfSW (sw, faces, curr, next);
    h=nh; hP=nhP;

    CE ce;
    while (true)
    {
        if (solveAtomicSW ( ~(v(inits) |= v(nh)) ))
            ce = getCE(true, curr);
        else if (solveAtomicSW ( ~(v(nh) |= ~v(bads)) ))
            ce = getCE(false, curr);
        else if (solveAtomicSW ( ~(v(nh)&v(trans) |= v(nhP)) ))
        {
            ce = getCE(v(bads), faces, curr, next);
            // prioritize transition pairs from last iteration
            if (solveAtomicSW ( ~(v(h)&v(trans) |= v(nhP)) ))
                ce = getCE(v(bads), faces, curr, next);
        }
        else
            break;

        if (ce.t) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce.v) )
                f.push_absorption(ce.v);
        }
        else // negative ce
        {
            if ( evalAtomicSW (ce.v, v(inits), curr) )
                return false;

            faces.push_back( Face(ce.v) );

            // update last iteration on restart
            releaseSW(sw);
            sw = newSW();
            tie(h,hP) = addCdnfSW (sw, faces, curr, next);
        }

        releaseSW(nsw);
        nsw = newSW();

        tie(nh,nhP) = addCdnfSW (nsw, faces, curr, next);
    
        // update last iteration when on subsumption
        if (!solveAtomicSW ( ~(v(h)&v(trans) |= v(nhP)) ))
        {
            releaseSW(sw);
            sw = newSW();
            tie(h,hP) = addCdnfSW (sw, faces, curr, next);
        }
    }

    releaseSW(sw);
    releaseSW(nsw);
    releaseStates(curr);
    releaseStates(next);

    return true;
}

// NOTE: what if: learn 'exact' formula(x) = Ex'.trans(x',x) and force it into h?
// NOTE: we can isolate the troubling states by hypt(x) & Ex'.trans(x,x')
//       question is what can we do with them?
// NOTE: info is most present at the nodes, viewpoints of faces, ie the bases
// NOTE: what can we do with hypercube of trans thats like two cube cubed?
// NOTE: trans is a set of edges between state cubes.
//       what if its a basis? what if its covered? what if its a prime?