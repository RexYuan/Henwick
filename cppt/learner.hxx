
#pragma once

#include <bitset>
#include <functional>
#include <vector>

template<std::size_t N>
inline bool operator<(const std::bitset<N>& lhs, const std::bitset<N>& rhs);

template<std::size_t N>
std::function<bool(const std::bitset<N>&)> mk_mterm_f(const std::bitset<N>& b1);

template<std::size_t N>
std::function<bool(const std::bitset<N>&)> mk_mdnf_f(const std::bitset<N>& basis, const std::vector<std::function<bool(const std::bitset<N>&)>>& term_fs);

template<std::size_t N>
std::function<bool(const std::bitset<N>&)> mk_conj_hypt(const std::vector<std::function<bool(const std::bitset<N>&)>>& dnf_fs);

template<std::size_t N>
void walk(std::bitset<N>& b, const std::bitset<N>& a, const std::function<bool(const std::bitset<N>&)>& f);

template<std::size_t N>
std::function<bool(std::bitset<N>)> fff(std::bitset<N>& a);