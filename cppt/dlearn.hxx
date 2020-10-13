
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
bool Ctx<N>::dlearn (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Step curr = addStates(); // current
    Step next = addStates(); // next

    Var fixed = newSW();
    Var inits = addBfSW(fixed, inits_, curr),
        bads  = addBfSW(fixed, bads_, curr),
        trans = addBfSW(fixed, trans_, curr);

    if (solveAtomicSW ( v(inits)&v(bads) )) // degen false
        return false;

    FaceVector faces;
    Var hypt, hyptP;
    bool pass = false;

    if (!solveAtomicSW( v(bads) )) // degen true
        return true;

    CE ce = dgetCE(false, curr);
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
            ce = dgetCE(true, curr);
        else if (solveAtomicSW ( ~(v(hypt) |= ~v(bads)) ))
            ce = dgetCE(false, curr);
        else if (solveAtomicSW ( ~(v(hypt)&v(trans) |= v(hyptP)) ))
            ce = dgetCE(v(bads), faces, curr, next);
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
Ctx<N>::CE Ctx<N>::dgetCE (bool t, Step curr)
{
    assert( s.okay() );

    string tmp;
    for (Var i=states[curr], h=i+N; i<h; i++)
        tmp += (s.model[i] == l_True) ? "1" : "0";

    return CE {mkBv(tmp), t};
}

template <size_t N>
Ctx<N>::CE Ctx<N>::dgetCE (Bf_ptr bads, const FaceVector& faces, Step curr, Step next)
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

template <size_t N>
pair<Var,Var> Ctx<N>::addCdnfSW (Var sw, const FaceVector& cdnf, Step curr, Step next)
{
    assert( s.nVars() >= N*2 );

    Var r = s.newVar(), rp = s.newVar();

    vec<Lit> rls, rpls;
    rls.push(mkLit(sw)); rpls.push(mkLit(sw));
    rls.push(mkLit(r)); rpls.push(mkLit(rp));
    for (Face dnf : cdnf)
    {
        Var dr = s.newVar(), drp = s.newVar();
        addClauseSW(sw, ~mkLit(r), mkLit(dr)); addClauseSW(sw, ~mkLit(rp), mkLit(drp));
        rls.push(~mkLit(dr)); rpls.push(~mkLit(drp));

        vec<Lit> dls, dpls;
        dls.push(mkLit(sw)); dpls.push(mkLit(sw));
        dls.push(~mkLit(dr)); dpls.push(~mkLit(drp));
        for (Bv term : dnf.primes)
        {
            Var cr = s.newVar(), crp = s.newVar();
            addClauseSW(sw, ~mkLit(cr), mkLit(dr)); addClauseSW(sw, ~mkLit(crp), mkLit(drp));
            dls.push(mkLit(cr)); dpls.push(mkLit(crp));

            vec<Lit> cls, cpls;
            cls.push(mkLit(sw)); cpls.push(mkLit(sw));
            cls.push(mkLit(cr)); cpls.push(mkLit(crp));
            for (Var i=0, c=states[curr], n=states[next]; i<N; i++, c++, n++)
            {
                if (term[i] == true && dnf.basis[i] == false)
                {
                    addClauseSW(sw, ~mkLit(cr), mkLit(c)); addClauseSW(sw, ~mkLit(crp), mkLit(n));
                    cls.push(~mkLit(c)); cpls.push(~mkLit(n));
                }
                else if (term[i] == false && dnf.basis[i] == true)
                {
                    addClauseSW(sw, ~mkLit(cr), ~mkLit(c)); addClauseSW(sw, ~mkLit(crp), ~mkLit(n));
                    cls.push(mkLit(c)); cpls.push(mkLit(n));
                }
            }
            addClauseSW(sw, cls); addClauseSW(sw, cpls);
        }
        addClauseSW(sw, dls); addClauseSW(sw, dpls);
    }
    addClauseSW(sw, rls); addClauseSW(sw, rpls);
    return make_pair(r,rp);
}