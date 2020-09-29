
#include <iostream>

using namespace std;

template <typename ...P>
concept at_most_3 = sizeof...(P) <= 3;

template <typename ...P>
concept all_ints = (std::same_as<P, int> && ...);

template <typename... Ts>
void foo (Ts... ts) // option 1
{
    (cout << ... << ts) << endl;
}

template <typename... Ts> requires at_most_3<Ts...>
void foo (Ts... ts) // option 2
{
    (cout << ... << ts) << endl;
}

template <typename... Ts> requires all_ints<Ts...>
void foo (Ts... ts) // option 3
{
    (cout << ... << ts) << endl;
}

template <typename... Ts> requires at_most_3<Ts...> && all_ints<Ts...>
void foo (Ts... ts) // option 4
{
    cout << "here!";
    (cout << ... << ts) << endl;
}

int main()
{
    foo(1,2);
}