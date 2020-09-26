
#pragma once

#include "ctx.hxx"
#include "bf.hxx"

/*template <size_t N>
void Ctx<N>::walk (Bv& b, const Bv& towards, Bf_ptr bads, const FaceVector& faces)
{
    auto in_bases = [&faces](const Bv& b)
    {
        for (const auto& f : faces)
        if (f.basis == b)
            return true;
        return false;
    };

    bool peaked = false;
    while (!peaked)
    {
        peaked = true;
        for (int i=0; i<N; i++)
        if (b[i] != towards[i])
        {
            b.flip(i);
            if (!solveAtomicSW (b, bads) && !in_bases(b))
            {
                peaked = false;
                break;
            }
            b.flip(i);
        }
    }
}*/

template <size_t N>
bool Ctx<N>::learn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
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
    
    update_ce(false);
    Var sw = newSW();
    while (!pass)
    {
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
            if (solveAtomicSW (ce, v(inits))) // the only way to return false once algo starts
                                              // when a decided neg ce is in inits meaning bads is
                                              // reachable from inits and refutation is possible
                return false;
            faces.push_back( Face(ce) );
        }

        tie(hypt,hyptP) = addCdnfSW (sw, faces);
        
        if (solveAtomicSW ( ~(v(inits) |= v(hypt)) ))
            update_ce(true);   
        else if (solveAtomicSW ( ~(v(hypt) |= ~v(bads)) ))
            update_ce(false);
        else if (solveAtomicSW ( ~(v(hypt)&v(trans) |= v(hyptP)) ))
            decide_ce(v(bads), faces);
        else
            pass = true;
        
        releaseSW(sw);
        sw = newSW();
    }
    
    cout << "passing true" << endl;
    cout << to_string(faces);
    return true;
}

template <size_t N>
void Ctx<N>::decide_ce (Bf_ptr bads, const FaceVector& faces) // determine ce when trans violated
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

    if (solveAtomicSW (succ, bads))
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