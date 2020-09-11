
#include <iostream>
#include <bitset>
#include <functional>
#include <vector>

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

template<std::size_t N>
class Learner
{
    using bs = std::bitset<N>;
    using bf = std::function<bool(bs)>;
private:
    bs ce;
    std::vector<bs> bases;
    std::vector<std::vector<bs>> learnd_terms;
    std::vector<std::vector<bf>> hypted_termfs;
    std::vector<bf> hypted_dnffs;
    bf conj_hypts;
public:
    explicit Learner(/* args */);
    ~Learner();
};

template<std::size_t N>
Learner<N>::Learner(/* args */)
{
}

template<std::size_t N>
Learner<N>::~Learner()
{
}


int main()
{
    std::bitset<5> b1("10010");
    std::bitset<5> b2("00001");
    std::bitset<5> b3("11011");
    std::function<bool(const std::bitset<5>&)> f1 = mk_mterm_f(b1);
    std::function<bool(const std::bitset<5>&)> f2 = mk_mterm_f(b2);
    std::vector<std::function<bool(const std::bitset<5>&)>> fs;
    fs.push_back(f1);
    fs.push_back(f2);
    auto m = mk_conj_hypt(fs);
    int a=3;
    if (false && (a=2))
    a=5;
    std::cout << m(b3);
}