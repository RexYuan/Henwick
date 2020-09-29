
#pragma once

#include "ctx.hxx"

template <size_t N>
inline Var Ctx<N>::newSW () { Var sw=s.newVar(); activeSW.insert(sw); return sw; }
template <size_t N>
inline void Ctx<N>::releaseSW (Var sw) { activeSW.erase(sw); inactiveSW.erase(sw); s.releaseVar(mkLit(sw)); }
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
bool Ctx<N>::solveAtomicSW (Step step, const Bv& bv, const Bf_ptr& bf) // if bv is in bf
{
    vec<Lit> tmp;
    for (Var i=states[step], h=i+N; i<h; i++)
        if (bv[i]) tmp.push( mkLit(i) );
        else tmp.push( ~mkLit(i) );
    Var e = newSW();
    tmp.push(mkLit(addBfSW(e, bf)));
    bool ret = solveSW(tmp);
    releaseSW(e);
    return ret;
}

template <size_t N>
Var Ctx<N>::addBfSW (Var sw, const Bf_ptr& bf)
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
        return bf->get_int();
        break;    
    case Conn::Not:
    {
        Var v = s.newVar();
        Var sub_v = addBfSW(sw, bf->get_range()[0]);
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
            sub_v = addBfSW(sw, sub);
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
            sub_v = addBfSW(sw, sub);
            addClauseSW(sw, mkLit(v), ~mkLit(sub_v));
            l.push(mkLit(sub_v));
        }
        addClauseSW(sw, l);
        return v;
        break;
    }
    }
    assert( false );
}

// NOTE: reserverd for step wise single cdnf formula adding for blearn
template <size_t N>
pair<Var,Var> Ctx<N>::addCdnfSW (Step step, Var sw, const FaceVector& cdnf)
{
    return make_pair(0,0);
}