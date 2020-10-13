
#pragma once

#include "ctx.hxx"

template <size_t N>
Ctx<N>::Step Ctx<N>::beginStates () const
{
    return released.size();
}

template <size_t N>
Ctx<N>::Step Ctx<N>::endStates () const
{
    return states.size();
}

template <size_t N>
Ctx<N>::Step Ctx<N>::nStates () const
{
    return states.size()-released.size();
}

template <size_t N>
Ctx<N>::Step Ctx<N>::addStates ()
{
    states[states.size()]=s.nVars();
    for (size_t i=0; i<N; i++)
        s.newVar();
    return states.size()-1;
}

template <size_t N>
void Ctx<N>::releaseStates (Step step)
{
    for (Var i=states[step], h=i+N; i<h; i++)
        s.releaseVar(mkLit(i));
    released.insert(step);
}

template <size_t N>
void Ctx<N>::tabulate ()
{
    assert( nStates() > 0 );
    cout << "listing truth table:" << endl;
    
    auto to_bs = [&](int i) -> string
    {
        string s;
        for (int j=0; j<N; j++, i>>=1)
            if (1&i) s = "1"+s;
            else s = "0"+s;
        return s;
    };
    auto baseHelper = [&](string bss) -> void
    {
        vec<Lit> tmp;
        for (Step s=0, nS=nStates(), si=beginStates(); s<nS; s++, si++)
        for (Var b=0; b<N; b++){
            if (bss[N*s+b]=='1') tmp.push(mkLit(b+states[si]));
            else tmp.push(~mkLit(b+states[si]));}

        for (int s=0, nS=nStates(); s<nS; s++)
            bss.insert(N*s+s, " ");
        cout << bss << " " << solveSW(tmp) << endl;
    };
    function<void(string,unsigned int)> recurHelper;
    recurHelper = [&to_bs,&baseHelper,&recurHelper](string prefix, unsigned int depth) -> void
    {
        if (depth == 0)
            baseHelper(prefix);
        else
            for (unsigned int i=0; i<pow(2,N); i++)
                recurHelper(prefix+to_bs(i), depth-1);
    };

    recurHelper("", nStates());
}

template <size_t N>
void Ctx<N>::tabulate (Step step)
{
    assert( nStates() > step );
    cout << "listing truth table of step " << step << ":" << endl;
    vec<Lit> tmp;
    for (int i=0, offset=states[step]; i<pow(2,N); i++)
    {
        Bv tmp_b (i);
        for (int j=0; j<N; j++)
            if (tmp_b[j]) tmp.push(mkLit(j+offset));
            else tmp.push(~mkLit(j+offset));
        
        cout << to_string(tmp_b) << " " << solveSW(tmp) << endl;
        tmp.clear();
    }
}