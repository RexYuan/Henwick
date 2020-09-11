
#include <iostream>
#include <bitset>
#include <functional>

#include "template.hxx"

extern std::bitset<3> b1,b2;
extern std::function<bool(std::bitset<3>)> f1,f2;

int main()
{
    std::cout << (f1(b1) == f1(b1));
}