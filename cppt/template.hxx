
#pragma once
#include <iostream>
#include <bitset>
#include <functional>

template<std::size_t N>
std::function<bool(std::bitset<N>)> fff(std::bitset<N>& a)
{
    return [&a](std::bitset<N> b)
    {
        return a==b;
    };
}