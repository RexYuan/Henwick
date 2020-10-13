
#pragma once

#include "ctx.hxx"
#include "bf.hxx"

template <size_t N>
bool Ctx<N>::mlearn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Step curr = addStates();
    Step next = addStates();

    Var fixed = newSW(), suffSW = newSW();
    Var inits = addBfSW(fixed, inits_, curr),
        bads  = addBfSW(suffSW, bads_, curr),
        trans = addBfSW(fixed, trans_, curr, next);
    
    if (!solveAtomicSW( v(bads) )) return true;
    if (solveAtomicSW ( v(inits)&v(bads) )) return false;

    Var hypt = inits, nhypt = inits;

    vector<Step> suffSteps = {next};
    releaseSW(suffSW);
    suffSW = newSW();

    Var sbads = addBfSW(suffSW, bads_, next);
    Var strans;
    Bf_ptr suffbads = v(sbads);
    Bf_ptr sufftrans = v(true);

    Var sw = newSW();
    while (true)
    {
        while (solveAtomicSW ( v(hypt)&v(trans) & sufftrans&suffbads )) // reaching bads
        {
            if (!solveAtomicSW ( ~(v(hypt) |= v(inits)) )) // refutation ready
                return false;
            else // advance bads suffix
            { 
                suffSteps.push_back( addStates() );
                sbads = addBfSW(suffSW, bads_, suffSteps[suffSteps.size()-1]);
                strans = addBfSW(suffSW, trans_, suffSteps[suffSteps.size()-2], suffSteps[suffSteps.size()-1]);
                suffbads = suffbads | v(sbads);
                sufftrans = sufftrans & v(strans);

                if( solveAtomicSW ( v(inits)&v(trans) & sufftrans&suffbads ) ) // refutation ready
                    return false;

                hypt = deployCdnfAtomic (sw, inits, trans, sufftrans, suffbads, curr, next);
            }
        }

        // advance image overapprox
        nhypt = deployCdnfAtomic (sw, hypt, trans, sufftrans, suffbads, curr, next);
        
        if (!solveAtomicSW ( ~(v(nhypt) |= v(hypt)) )) // invariant found
            break;
        hypt = nhypt;
    }

    releaseSW(fixed);
    releaseSW(suffSW);
    releaseSW(sw);
    releaseStates(curr);
    for (auto s : suffSteps)
        releaseStates(s);

    return true;
}

template <size_t N>
Var Ctx<N>::deployCdnfAtomic (Var sw, Var hypt, Var trans, Bf_ptr sufftrans, Bf_ptr suffbads, Step curr, Step next)
{
    // interpolant must be unsat to obtain
    assert ( !solveAtomicSW ( v(hypt)&v(trans) & sufftrans&suffbads ) );
    
    FaceVector faces;
    Var h, hP; // statespace of target hP to be in `next` while last hypt statespace is `curr`
    bool pass = false;

    // suffix must be nonempty
    assert (solveAtomicSW( sufftrans&suffbads ));

    // statespace `next` is the shared state between prem and suff
    CE ce = dgetCE(false, next);
    Var tmp_sw = newSW();
    while (!pass)
    {
        if (ce.t) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce.v) ) // exact cdnf, walk is possible but not implemented
                f.push_absorption(ce.v);
        }
        else // negative ce
        {
            faces.push_back( Face(ce.v) );
        }
        
        tie(h,hP) = addCdnfSW (tmp_sw, faces, curr, next);
        
        if (solveAtomicSW ( ~(v(hypt) |= v(h)) ))
            ce = dgetCE(true, curr);
        else if (solveAtomicSW ( ~(v(hypt)&v(trans) |= v(hP)) ))
            ce = dgetCE(true, next);
        else if (solveAtomicSW ( ~(v(hP) |= ~(sufftrans&suffbads)) ))
            ce = dgetCE(false, next);
        else
            pass = true;
        
        releaseSW(tmp_sw);
        tmp_sw = newSW();
    }

    releaseSW(tmp_sw);

    // sw was the last iteration's switch
    releaseSW(sw);
    sw = newSW();
    h = addCdnfSW (sw, faces, curr);

    //cout << to_string(faces) << flush;
    return h;
}