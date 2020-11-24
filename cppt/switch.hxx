
#pragma once

#include "ctx.hxx"

template <size_t N>
inline Var Ctx<N>::newSW () { Var sw=s.newVar(); activeSW.insert(sw); return sw; }
template <size_t N>
inline void Ctx<N>::releaseSW (Var sw) { activeSW.erase(sw); inactiveSW.erase(sw); s.addClause(mkLit(sw)); 
/*s.releaseVar(mkLit(sw));*/ }
template <size_t N>
inline void Ctx<N>::activate (Var sw) { inactiveSW.erase(sw); activeSW.insert(sw); }
template <size_t N>
inline void Ctx<N>::deactivate (Var sw) { activeSW.erase(sw); inactiveSW.insert(sw); }

template <size_t N>
template <typename... Ts> requires (sizeof...(Ts)<=3) && (same_as<Ts, Lit> && ...)
inline bool Ctx<N>::addClauseSW (Var sw, Ts... lits) { return s.addClause(mkLit(sw), lits...); }
template <size_t N>
template <typename... Ts> requires (sizeof...(Ts)>3) && (same_as<Ts, Lit> && ...)
inline bool Ctx<N>::addClauseSW (Var sw, Ts... lits) { vec<Lit> ps; (ps.push(lits), ...); return addClauseSW(sw, ps); }
template <size_t N>
inline bool Ctx<N>::addClauseSW (Var sw, const vec<Lit>& ps) { vec<Lit> tmp; ps.copyTo(tmp); tmp.push(mkLit(sw)); return s.addClause_(tmp); }

template <size_t N>
template <typename... Ts> requires (same_as<Ts, Lit> && ...)
bool Ctx<N>::solveSW (Ts... lits)
{
    vec<Lit> ps; (ps.push(lits), ...);
    return solveSW(ps);
}

template <size_t N>
bool Ctx<N>::solveSW (const vec<Lit>& ps)
{
    vec<Lit> tmp; ps.copyTo(tmp);
    for (auto sw :   activeSW) tmp.push(~mkLit(sw));
    for (auto sw : inactiveSW) tmp.push( mkLit(sw));
    return s.solve(tmp);
}

template <size_t N>
bool Ctx<N>::solveAtomicSW (const Bf_ptr& bf)
{
    Var e = newSW();
    bool ret = solveSW(mkLit(addBfSW(e, bf)));
    releaseSW(e);
    return ret;
}

template <size_t N>
bool Ctx<N>::evalAtomicSW (const Bv& bv, const Bf_ptr& bf, optional<Step> step) // if bv is in bf
{
    vec<Lit> tmp;
    for (Var i=0, h=i+N, offset=(step?states[step.value()]:0); i<h; i++)
        if (bv[i]) tmp.push( mkLit(i+offset) );
        else tmp.push( ~mkLit(i+offset) );
    Var e = newSW();
    tmp.push(mkLit(addBfSW( e, bf )));
    bool ret = solveSW(tmp);
    releaseSW(e);
    return ret;
}

template <size_t N>
Var Ctx<N>::addBfSW (Var sw, const Bf_ptr& bf, optional<Step> step1, optional<Step> step2)
{
    switch (bf->t)
    {
    case Conn::Top:
    {
        Var v = s.newVar();
        addClauseSW(sw, mkLit(v));
        return v;
        break;
    }
    case Conn::Bot:
    {
        Var v = s.newVar();
        addClauseSW(sw, ~mkLit(v));
        return v;
        break;
    }
    case Conn::Base:
    {
        if (step1 && step2)
        {
            if ( bf->get_int() < N )
                return states[step1.value()]+bf->get_int();
            else if ( N <= bf->get_int() && bf->get_int() < N+N )
                return states[step2.value()]+bf->get_int()-N;
            else throw runtime_error( "user v out of range: "+std::to_string(bf->get_int()) );
        }
        else if (step1)
        {
            cout << "step input is " << step1.value() << endl;
            if ( bf->get_int() < N+N )
                return states[step1.value()]+bf->get_int();
            else throw runtime_error( "user v out of range: "+std::to_string(bf->get_int()) );
        }
        else
        {
            return bf->get_int();
        }
        break;
    }
    case Conn::Not:
    {
        Var v = s.newVar();
        Var sub_v = addBfSW(sw, bf->get_range()[0], step1, step2);
        addClauseSW(sw,  mkLit(v),  mkLit(sub_v));
        addClauseSW(sw, ~mkLit(v), ~mkLit(sub_v));
        return v;
        break;
    }
    case Conn::And:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push(mkLit(v));
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBfSW(sw, sub, step1, step2);
            addClauseSW(sw, ~mkLit(v), mkLit(sub_v));
            l.push(~mkLit(sub_v));
        }
        addClauseSW(sw, l);
        return v;
        break;
    }
    case Conn::Or:
    {
        Var v = s.newVar();
        vec<Lit> l;
        l.push(~mkLit(v));
        for (Var sub_v; Bf_ptr sub : bf->get_range())
        {
            sub_v = addBfSW(sw, sub, step1, step2);
            addClauseSW(sw, mkLit(v), ~mkLit(sub_v));
            l.push(mkLit(sub_v));
        }
        addClauseSW(sw, l);
        return v;
        break;
    }
    }
    cout << bf << " the fuck ?" << endl;
    assert( false );
}

template <size_t N>
Var Ctx<N>::addCdnfSW (Var sw, const FaceVector& cdnf, optional<Step> step)
{
    assert( s.nVars() >= N );

    if (cdnf.size() == 0)
        return constTrue;

    Var r = s.newVar();

    vec<Lit> rls;
    rls.push(mkLit(sw));
    rls.push(mkLit(r));
    for (const Face& dnf : cdnf)
    {
        Var dr = s.newVar();
        addClauseSW(sw, ~mkLit(r), mkLit(dr));
        rls.push(~mkLit(dr));

        vec<Lit> dls;
        dls.push(mkLit(constFalse)); // identity element of disjunction
                                     // force empty dnf be constant false
        dls.push(mkLit(sw));
        dls.push(~mkLit(dr));
        for (const Bv& term : dnf.primes)
        {
            Var cr = s.newVar();
            addClauseSW(sw, ~mkLit(cr), mkLit(dr));
            dls.push(mkLit(cr));

            vec<Lit> cls;
            cls.push(mkLit(sw));
            cls.push(mkLit(cr));
            for (Var i=0, offset=(step?states[step.value()]:0); i<N; i++)
            {
                if (term[i] == true && dnf.basis[i] == false)
                {
                    addClauseSW(sw, ~mkLit(cr), mkLit(i+offset));
                    cls.push(~mkLit(i+offset));
                }
                else if (term[i] == false && dnf.basis[i] == true)
                {
                    addClauseSW(sw, ~mkLit(cr), ~mkLit(i+offset));
                    cls.push(mkLit(i+offset));
                }
            }
            addClauseSW(sw, cls);
        }
        addClauseSW(sw, dls);
    }
    addClauseSW(sw, rls);
    return r;
}

template <size_t N>
pair<Var,Var> Ctx<N>::addCdnfSW (Var sw, const FaceVector& cdnf, Step curr, Step next)
{
    assert( s.nVars() >= N*2 );

    if (cdnf.size() == 0)
        return make_pair(constTrue,constTrue);

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
        rls.push(mkLit(constFalse)); rpls.push(mkLit(constFalse));
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