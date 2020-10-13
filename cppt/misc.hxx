
#pragma once

#include "ctx.hxx"

template <size_t N>
Ctx<N>::Bv Ctx<N>::mkBv (string s)
{
    reverse(s.begin(), s.end());
    return Bv (s);
}

template <size_t N>
Ctx<N>::BvVector Ctx<N>::mkBvs (initializer_list<string> ss)
{
    BvVector bvs {};
    for (string s : ss) bvs.push_back(mkBv(s));
    return bvs;
}

template <size_t N>
string Ctx<N>::to_string (const Bv& bs)
{
    string s = bs.to_string();
    reverse(s.begin(), s.end());
    return s;
}

template <size_t N>
string Ctx<N>::to_string (const Face& f)
{
    string s = "";
    s += to_string(f.basis) + ", {";
    if (f.primes.size()>0)
        s += to_string(f.primes[0]);
    for (size_t i=1; i<f.primes.size(); i++)
        s += ", " + to_string(f.primes[i]);
    s += "}\n";
    return s;
}

template <size_t N>
string Ctx<N>::to_string (const FaceVector& fs)
{
    string s = "";
    for (auto f : fs)
        s += to_string(f);
    return s;
}

template <size_t N>
Bf_ptr Ctx<N>::substitute (Bf_ptr bf, Step from, Step to)
{
    switch (bf->t)
    {
    case Conn::Top:
    case Conn::Bot: return bf;
    case Conn::Base:
        if (  states[from] <= bf->get_int() && bf->get_int() < states[from]+N )
            return v( (bf->get_int()-states[from]) + states[to] );
        else
            return bf;
    case Conn::Not: return ~substitute(bf->get_range()[0], from, to);
    case Conn::And:
    case Conn::Or:
    {
        Bf_ptr tmp = make_shared<Bf>( bf->t );
        for (Bf_ptr sub : bf->get_range())
            tmp->push( substitute(sub, from, to) );
        return tmp;
    }
    }
    assert( false );
}

template <size_t N>
string Ctx<N>::to_string (const CE& ce)
{
    string tmp = "";
    tmp+="(";
    tmp+=(ce.t ? "T" : "F");
    tmp+=") ";
    tmp+=to_string(ce.v);
    return tmp;
}