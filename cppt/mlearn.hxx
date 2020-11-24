
#pragma once

#include "ctx.hxx"
#include "bf.hxx"

template <size_t N>
bool Ctx<N>::mlearn (string filename)
{
    vector<Var> input_to_var_map;
    minputInputAAG (filename, input_to_var_map);

    Step curr = addStates(),
         next = addStates();
    vector<Var> curr_aag_to_var_map,
                next_aag_to_var_map;
    minputStateAAG (filename, input_to_var_map, curr_aag_to_var_map, curr);
    minputStateAAG (filename, input_to_var_map, next_aag_to_var_map, next);
    
    Var suffSW = newSW();
    Var inits = minputGetInitsAAG (fixedSW, curr),
        bads  = minputGetBadsAAG (suffSW, filename, curr_aag_to_var_map, curr),
        trans = minputGetTransAAG (fixedSW, filename, curr_aag_to_var_map, curr, next);
    
    if (!solveAtomicSW( v(bads) )) return true;
    if (solveAtomicSW ( v(inits)&v(bads) )) return false;

    Var hypt = inits, nhypt = inits;

    vector<Step> suffSteps = {next};
    vector<vector<Var>> suff_aag_to_var_maps = {next_aag_to_var_map};
    releaseSW(suffSW);
    suffSW = newSW();

    Var sbads = minputGetBadsAAG (suffSW, filename, next_aag_to_var_map, next);
    Var strans;
    Bf_ptr suffbads = v(sbads);
    Bf_ptr sufftrans = v(true);

    Var sw = newSW();
    unsigned long long i = 0;
    while (true)
    {
        //cout << "outer: " << i++ << endl << flush;
        while (solveAtomicSW ( v(hypt)&v(trans) & sufftrans&suffbads )) // reaching bads
        {
            //cout << "inner: " << suffSteps.size() << endl << flush;
            if (!solveAtomicSW ( ~(v(hypt) |= v(inits)) )) // refutation ready
                return false;
            else // advance bads suffix
            {
                suffSteps.push_back( addStates() );
                suff_aag_to_var_maps.emplace_back();
                minputStateAAG (filename, input_to_var_map, suff_aag_to_var_maps[suff_aag_to_var_maps.size()-1], suffSteps[suffSteps.size()-1]);

                sbads = minputGetBadsAAG (suffSW, filename, suff_aag_to_var_maps[suff_aag_to_var_maps.size()-1], suffSteps[suffSteps.size()-1]);
                strans = minputGetTransAAG (fixedSW, filename, suff_aag_to_var_maps[suff_aag_to_var_maps.size()-1], suffSteps[suffSteps.size()-1], suffSteps[suffSteps.size()-2]);
                suffbads = suffbads | v(sbads);
                sufftrans = sufftrans & v(strans);

                if( solveAtomicSW ( v(inits)&v(trans) & sufftrans&suffbads ) ) // refutation ready
                    return false;

                releaseSW(sw);
                sw = newSW();
                hypt = deployCdnfAtomic (sw, inits, trans, sufftrans, suffbads, curr, next, suffSteps);
            }
        }

        // advance image overapprox
        nhypt = deployCdnfAtomic (sw, hypt, trans, sufftrans, suffbads, curr, next, suffSteps);
        
        if (!solveAtomicSW ( ~(v(nhypt) |= v(hypt)) )) // invariant found
            break;
        hypt = nhypt;
    }

    releaseSW(suffSW);
    releaseSW(sw);
    releaseStates(curr);
    for (auto s : suffSteps)
        releaseStates(s);

    return true;
}

template <size_t N>
bool Ctx<N>::mlearn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Step curr = addStates();
    Step next = addStates();

    Var suffSW = newSW();
    Var inits = addBfSW(fixedSW, inits_, curr),
        bads  = addBfSW(suffSW, bads_, curr),
        trans = addBfSW(fixedSW, trans_, curr, next);
    
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
    unsigned long long i = 0;
    while (true)
    {
        //cout << "outer: " << i++ << endl << flush;
        while (solveAtomicSW ( v(hypt)&v(trans) & sufftrans&suffbads )) // reaching bads
        {
            //cout << "inner: " << suffSteps.size() << endl << flush;
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

                releaseSW(sw);
                sw = newSW();
                hypt = deployCdnfAtomic (sw, inits, trans, sufftrans, suffbads, curr, next, suffSteps);
            }
        }

        // advance image overapprox
        nhypt = deployCdnfAtomic (sw, hypt, trans, sufftrans, suffbads, curr, next, suffSteps);
        
        if (!solveAtomicSW ( ~(v(nhypt) |= v(hypt)) )) // invariant found
            break;
        hypt = nhypt;
    }

    releaseSW(suffSW);
    releaseSW(sw);
    releaseStates(curr);
    for (auto s : suffSteps)
        releaseStates(s);

    return true;
}

/*
    return an added formula H in statespace `curr` on switch `sw` such that these holds:
    (1) hypt => H
    (2) H => ~(suffix induced by `sufftrans` & `suffbads`)
    (3) hypt(curr) & trans(curr,next) => H(next)

    that is, an forward image overapprox of hypt, learned using cdnf
*/
template <size_t N>
Var Ctx<N>::deployCdnfAtomic (Var sw, Var hypt, Var trans, Bf_ptr sufftrans, Bf_ptr suffbads, Step curr, Step next, vector<Step> suffSteps)
{
    // interpolant must be unsat to obtain
    assert ( !solveAtomicSW ( v(hypt)&v(trans) & sufftrans&suffbads ) );
    
    FaceVector faces;
    Var h, hP; // statespace of target hP to be in `next` while last hypt statespace is `curr`
    bool pass = false;

    // suffix must be nonempty
    assert (solveAtomicSW( sufftrans&suffbads ));

    // statespace `next` is the shared state between prem and suff
    CE ce = getCE(false, next);
    Var tmp_sw = newSW();
    while (!pass)
    {
        if (ce.t) // positive ce
        {
            for (auto& f : faces)
            if ( !f(ce.v) ) // exact cdnf, walk is possible but not used since its slower
            {
                //walk (ce.v, f.basis, hypt, trans, sufftrans, suffbads, curr, next, suffSteps);
                f.push_absorption(ce.v);
            }
        }
        else // negative ce
        {
            faces.push_back( Face(ce.v) );
        }
        
        tie(h,hP) = addCdnfSW (tmp_sw, faces, curr, next);
        
        if (solveAtomicSW ( ~(v(hypt) |= v(h)) ))
            ce = getCE(true, curr);
        else if (solveAtomicSW ( ~(v(hypt)&v(trans) |= v(hP)) ))
            ce = getCE(true, next);
        else if (solveAtomicSW ( ~(v(hP) |= ~(sufftrans&suffbads)) ))
            ce = getCE(false, next);
        else
            pass = true;
        
        releaseSW(tmp_sw);
        tmp_sw = newSW();
    }

    releaseSW(tmp_sw);

    h = addCdnfSW (sw, faces, curr);

    //cout << to_string(faces) << flush;
    return h;
}

/*
    walk (alter in place) from `b` towards `a` while keeping
    (1) inits(b) | (inits(fresh) & trans(fresh, b))
    (2) not in suffix induced by `sufftrans` & `suffbads`
*/
template <size_t N>
void Ctx<N>::walk (Bv& b, const Bv& a, Var inits, Var trans, Bf_ptr sufftrans, Bf_ptr suffbads, Step curr, Step next, vector<Step> suffSteps)
{
    auto in_suffix = [this, &sufftrans, &suffbads, &suffSteps](const Bv& b)
    {
        for (Step s : suffSteps)
        if ( evalAtomicSW (b, sufftrans&suffbads, s) )
            return true;
        return false;
    };

    bool peaked = false;
    while (!peaked)
    {
        peaked = true;
        for (int i=0; i<N; i++)
        if (b[i] != a[i])
        {
            b.flip(i);
            if ( (evalAtomicSW (b, v(inits), curr) || evalAtomicSW (b, v(inits)&v(trans), next)) && // cond (1)
                 (!in_suffix(b)) ) // cond (2)
            {
                peaked = false;
                break;
            }
            b.flip(i);
        }
    }
}