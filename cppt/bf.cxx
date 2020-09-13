
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

#include "bf.hxx"

using namespace std;

Bf::Bf (bool b) : sub {monostate{}} { if (b) t=Conn::Top; else t=Conn::Bot; };
Bf::Bf (int i) : t {Conn::Base}, sub {int{i}} {};
Bf::Bf (Conn c) : t {c}, sub {vector<Bf_ptr>{}} {};
Bf::Bf (Conn c, Bf_ptr bf) : t {c}, sub {vector<Bf_ptr>{bf}} {};

void Bf::push (Bf_ptr bf)
{
    assert( holds_alternative<vector<Bf_ptr>>(sub) );
    get<vector<Bf_ptr>>(sub).push_back(bf);
}

bool Bf::get_bool ()
{
    switch (t)
    {
    case Conn::Top: return true; break;
    case Conn::Bot: return false; break;
    }
    assert( false );
}

int Bf::get_int ()
{
    return get<int>(sub);
}

vector<Bf_ptr> Bf::get_range ()
{
    return get<vector<Bf_ptr>>(sub);
}

string Bf::to_string ()
{
    switch (t)
    {
    case Conn::Top: return "t"; break;
    case Conn::Bot: return "f"; break;
    case Conn::Base: return std::to_string( get<int>(sub) ); break;
    case Conn::Not: return "~"+get<vector<Bf_ptr>>(sub)[0]->to_string(); break;
    case Conn::And:
    {
        string tmp = "(";
        for (Bf_ptr s : get_range())
            tmp.append( s->to_string() + "&" );
        tmp.pop_back();
        tmp.append(")");
        return tmp;
        break;
    }
    case Conn::Or:
    {
        string tmp = "(";
        for (Bf_ptr s : get_range())
            tmp.append( s->to_string() + "|" );
        tmp.pop_back();
        tmp.append(")");
        return tmp;
        break;
    }
    }
    assert( false );
}

Bf_ptr v(bool b) { return make_shared<Bf>(b); }
Bf_ptr v(int i) { return make_shared<Bf>(i); }

Bf_ptr neg(Bf_ptr bf)
{
    switch (bf->t)
    {
    case Conn::Top: return v(false); break;
    case Conn::Bot: return v(true); break;
    case Conn::Not: return bf->get_range()[0]; break;
    default: return make_shared<Bf>(Conn::Not, bf);
    }
}

Bf_ptr conj(Bf_ptr bf1, Bf_ptr bf2)
{
    if (bf1->t == Conn::Bot ||
        bf2->t == Conn::Bot) return v(false);
    else if (bf1->t == Conn::Top) return bf2;
    else if (bf2->t == Conn::Top) return bf1;
    else if (bf1->t == Conn::And &&
             bf2->t == Conn::And)
    {
        for (auto s : bf2->get_range())
            bf1->push(s);
        return bf1;
    }
    else if (bf1->t == Conn::And)
    {
        bf1->push(bf2);
        return bf1;
    }
    else if (bf2->t == Conn::And)
    {
        bf2->push(bf1);
        return bf2;
    }
    else
    {
        return make_shared<Bf>( Conn::And, bf1, bf2 );
    }
}

Bf_ptr disj(Bf_ptr bf1, Bf_ptr bf2)
{
    if (bf1->t == Conn::Top ||
        bf2->t == Conn::Top) return v(true);
    else if (bf1->t == Conn::Bot) return bf2;
    else if (bf2->t == Conn::Bot) return bf1;
    else if (bf1->t == Conn::Or &&
             bf2->t == Conn::Or)
    {
        for (auto s : bf2->get_range())
            bf1->push(s);
        return bf1;
    }
    else if (bf1->t == Conn::Or)
    {
        bf1->push(bf2);
        return bf1;
    }
    else if (bf2->t == Conn::Or)
    {
        bf2->push(bf1);
        return bf2;
    }
    else
    {
        return make_shared<Bf>( Conn::Or, bf1, bf2 );
    }
}