
#include <bitset>
#include <functional>
#include <vector>

#include "learner.hxx"

template<std::size_t N>
inline bool operator<(const std::bitset<N>& lhs, const std::bitset<N>& rhs)
{
    return ((lhs & rhs) == lhs);
}

template<std::size_t N>
std::function<bool(const std::bitset<N>&)> mk_mterm_f(const std::bitset<N>& b1)
{
    return [&b1](const std::bitset<N>& b2)
    {
        return (b1<b2);
    };
}

template<std::size_t N>
std::function<bool(const std::bitset<N>&)> mk_mdnf_f(const std::bitset<N>& basis, const std::vector<std::function<bool(const std::bitset<N>&)>>& term_fs)
{
    return [&term_fs](const std::bitset<N>& b)
    {
        for (auto f : term_fs)
            if (f(b))
                return true;
        return false;
    };
}

template<std::size_t N>
std::function<bool(const std::bitset<N>&)> mk_conj_hypt(const std::vector<std::function<bool(const std::bitset<N>&)>>& dnf_fs)
{
    return [&dnf_fs](const std::bitset<N>& b)
    {
        for (auto f : dnf_fs)
            if (!f(b))
                return false;
        return true;
    };
}

template<std::size_t N>
void walk(std::bitset<N>& b, const std::bitset<N>& a, const std::function<bool(const std::bitset<N>&)>& f)
{
    bool more = true;
    while (more)
    {
        more = false;
        for (int i=0; i < N; i++)
            if ( b[i] != a[i] )
                if ( f(b.flip(i)) && (more=true) ) break;
                else b.flip(i);
    }
}

template<int N>
std::function<bool(std::bitset<N>)> fff(std::bitset<N>& a)
{
    return [&i](std::bitset<N> b)
    {
        return a==b;
    };
}