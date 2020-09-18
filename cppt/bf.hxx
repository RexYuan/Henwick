
#pragma once

#include <iostream>
#include <algorithm>
#include <bitset>
#include <functional>
#include <vector>
#include <variant>
#include <memory>
#include <string>
#include <utility>

#include "minisat.hxx"

using namespace std;

struct Bf;
enum class Conn {Top, Bot, Base, Not, And, Or};
using Bf_ptr = shared_ptr<Bf>;
template <typename T> concept is_Bf_ptr = same_as<T, Bf_ptr>;
template <typename... Ts> concept are_Bf_ptrs = (is_Bf_ptr<Ts> && ...);
struct Bf
{
    Conn t;
    variant<monostate, int, vector<Bf_ptr>> sub;

    Bf (bool b);
    Bf (int i);
    Bf (Conn c);
    Bf (Conn c, Bf_ptr bf);
    template <typename... Ts> requires are_Bf_ptrs<Ts...>
    Bf (Conn c, Ts... bfs) : t {c}, sub {vector<Bf_ptr>{bfs...}} {}
    
    void push (Bf_ptr bf);

    bool get_bool ();
    int get_int ();
    vector<Bf_ptr> get_range ();

    string to_string ();
};

Bf_ptr v(bool b);
Bf_ptr v(int i);
Bf_ptr neg(Bf_ptr bf);
Bf_ptr conj(Bf_ptr bf1, Bf_ptr bf2);
Bf_ptr disj(Bf_ptr bf1, Bf_ptr bf2);

inline Bf_ptr operator~(Bf_ptr bf) { return neg(bf); };
inline Bf_ptr operator&(Bf_ptr bf1, Bf_ptr bf2) { return conj(bf1,bf2); };
inline Bf_ptr operator|(Bf_ptr bf1, Bf_ptr bf2) { return disj(bf1,bf2); };
inline Bf_ptr operator|=(Bf_ptr bf1, Bf_ptr bf2) { return ~bf1 | bf2; };
inline Bf_ptr operator==(Bf_ptr bf1, Bf_ptr bf2) { return (~bf1 | bf2) & (bf1 | ~bf2); };
inline Bf_ptr operator!=(Bf_ptr bf1, Bf_ptr bf2) { return (bf1 | bf2) & (~bf1 | ~bf2); };

inline std::ostream& operator<<(std::ostream &out, Bf_ptr bf) { out << bf->to_string(); return out; }

Bf_ptr characteristic(string bs, int offset=0);
Bf_ptr counter(int bits);