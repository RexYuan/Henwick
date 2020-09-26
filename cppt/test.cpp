
#include <iostream>

using namespace std;

template <typename... Ts>
void foo (Ts... ts) // option 1
{
    (cout << ... << ts) << endl;
}

template <typename... Ts> requires (sizeof...(Ts)<=3)
void foo (Ts... ts) // option 2
{
    (cout << ... << ts) << endl;
}

template <typename... Ts> requires (same_as<Ts, int> && ...)
void foo (Ts... ts) // option 3
{
    (cout << ... << ts) << endl;
}

template <typename... Ts> requires (sizeof...(Ts)<=3) && (same_as<Ts, int> && ...)
void foo (Ts... ts) // option 4
{
    (cout << ... << ts) << endl;
}

int main()
{
    foo(1,2);
}