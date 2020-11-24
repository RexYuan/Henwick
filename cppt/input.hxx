
#pragma once

#include "ctx.hxx"

template <size_t N>
Ctx<N>::Problem Ctx<N>::inputBf (Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    return inputBf (fixedSW, fixedSW, fixedSW, inits_, bads_, trans_);
}

template <size_t N>
Ctx<N>::Problem Ctx<N>::inputBf (Var initsSW,   Var badsSW,   Var transSW,
                                 Bf_ptr inits_, Bf_ptr bads_, Bf_ptr trans_)
{
    Step curr = addStates(); // current
    Step next = addStates(); // next

    Var inits = addBfSW(initsSW, inits_, curr),
        bads  = addBfSW(badsSW, bads_, curr),
        trans = addBfSW(transSW, trans_, curr, next);

    return Problem (inits, bads, trans, curr, next);
}

template <size_t N>
Ctx<N>::Problem Ctx<N>::inputAAG (string filename)
{
    return inputAAG (fixedSW, fixedSW, fixedSW, filename);
}

template <size_t N>
Ctx<N>::Problem Ctx<N>::inputAAG (Var initsSW, Var badsSW, Var transSW,
                                  string filename)
{
    ifstream f(filename);
    assert( f );

    string title;
    int maxvar, Ninputs, Nlatches, Noutputs, Nands, output;
    f >> title >> maxvar >> Ninputs >> Nlatches >> Noutputs >> Nands;
    assert( Nlatches == N );
    assert( maxvar == Ninputs + Nlatches + Nands );

    vector<Var> aag_to_var_map;
    aag_to_var_map.resize(maxvar+1, -1);
    aag_to_var_map[0] = constFalse;

    // process inputs
    for (unsigned i=0, input; i<Ninputs; i++)
    {
        f >> input;
        aag_to_var_map[input >> 1] = s.newVar();
    }

    // process curr states
    ifstream::pos_type latches_pos = f.tellg();
    Step curr = addStates(s.nVars());
    for (unsigned i=0, c, n; i<Nlatches; i++)
    {
        f >> c >> n;
        aag_to_var_map[c >> 1] = s.newVar();
    }
    f >> output;

    // process ands
    for (unsigned i=0, lhs, rhs0, rhs1; i<Nands; i++)
    {
        f >> lhs >> rhs0 >> rhs1;
        aag_to_var_map[lhs >> 1] = s.newVar();

        Var lhsv = aag_to_var_map[lhs >> 1],
            rhs0v = (aag_to_var_map[rhs0 >> 1] > 0 ? aag_to_var_map[rhs0 >> 1] : s.newVar()),
            rhs1v = (aag_to_var_map[rhs1 >> 1] > 0 ? aag_to_var_map[rhs1 >> 1] : s.newVar());

        Lit lhsl = mkLit(lhsv),
            rhs0l = (rhs0 & 1 ? ~mkLit(rhs0v) : mkLit(rhs0v)),
            rhs1l = (rhs1 & 1 ? ~mkLit(rhs1v) : mkLit(rhs1v));

        s.addClause(~lhsl, rhs0l);
        s.addClause(~lhsl, rhs1l);
        s.addClause(~rhs0l, ~rhs1l, lhsl);
        //cout << "added " << lhsv << " = " << rhs0v << " ^ " << rhs1v << endl;
    }

    // process next states
    f.seekg(latches_pos);
    Step next = addStates(s.nVars());
    for (unsigned i=0; i<Nlatches; i++) s.newVar();

    Bf_ptr btrans = v(true);
    for (unsigned i=0, c, n; i<Nlatches; i++)
    {
        f >> c >> n;
        Var x = states[next]+i, xp = aag_to_var_map[n >> 1];
        assert( xp > 0 );

        Bf_ptr bx = v(x), bxp = (n & 1 ? ~v(xp) : v(xp));
        btrans = btrans & v(addBfSW(fixedSW, bx == bxp));
        //cout << "added " << x << " = " << xp << endl;
    }
    
    assert( aag_to_var_map[output >> 1] > 0 );
    Bf_ptr bbads = (output & 1 ? ~v(aag_to_var_map[output >> 1]) :
                                    v(aag_to_var_map[output >> 1]));

    string zeros = "";
    for (size_t i=0; i<N; i++) zeros += "0";
    Bf_ptr binits = characteristic(zeros, states[curr]);

    Var inits = addBfSW(initsSW, binits),
        bads = addBfSW(badsSW, bbads),
        trans = addBfSW(transSW, btrans);

    return Problem (inits, bads, trans, curr, next);
}

// initialize input_to_var_map
template <size_t N>
void Ctx<N>::minputInputAAG (string filename, vector<Var>& input_to_var_map)
{
    assert( input_to_var_map.size() == 0 );

    ifstream f(filename);
    assert( f );

    string title;
    int maxvar, Ninputs, Nlatches, Noutputs, Nands, output;
    f >> title >> maxvar >> Ninputs >> Nlatches >> Noutputs >> Nands;

    input_to_var_map.resize(Ninputs+1, -1);

    for (unsigned i=0, input; i<Ninputs; i++)
    {
        f >> input;
        input_to_var_map[input >> 1] = s.newVar();
    }
}

// initialize aag_to_var_map over added state step1
// and populate input, state, and ands info
template <size_t N>
void Ctx<N>::minputStateAAG (string filename, vector<Var>& input_to_var_map, vector<Var>& aag_to_var_map, Step step1)
{
    assert( aag_to_var_map.size() == 0 );

    ifstream f(filename);
    assert( f );

    string title;
    int maxvar, Ninputs, Nlatches, Noutputs, Nands, output;
    f >> title >> maxvar >> Ninputs >> Nlatches >> Noutputs >> Nands;

    assert( input_to_var_map.size() == Ninputs+1 );
    aag_to_var_map.resize(maxvar+1, -1);

    // copy inputs
    for (unsigned i=0, input; i<Ninputs; i++)
    {
        f >> input;
        aag_to_var_map[input >> 1] = input_to_var_map[input >> 1];
    }

    // put in states
    for (unsigned i=0, c, n; i<Nlatches; i++)
    {
        f >> c >> n;
        aag_to_var_map[c >> 1] = states[step1]+((c >> 1)-Ninputs-1);
    }
    f >> output;

    // put in ands
    for (unsigned i=0, lhs, rhs0, rhs1; i<Nands; i++)
    {
        f >> lhs >> rhs0 >> rhs1;
        aag_to_var_map[lhs >> 1] = s.newVar();

        Var lhsv = aag_to_var_map[lhs >> 1],
            rhs0v = (aag_to_var_map[rhs0 >> 1] > 0 ? aag_to_var_map[rhs0 >> 1] : s.newVar()),
            rhs1v = (aag_to_var_map[rhs1 >> 1] > 0 ? aag_to_var_map[rhs1 >> 1] : s.newVar());

        Lit lhsl = mkLit(lhsv),
            rhs0l = (rhs0 & 1 ? ~mkLit(rhs0v) : mkLit(rhs0v)),
            rhs1l = (rhs1 & 1 ? ~mkLit(rhs1v) : mkLit(rhs1v));

        s.addClause(~lhsl, rhs0l);
        s.addClause(~lhsl, rhs1l);
        s.addClause(~rhs0l, ~rhs1l, lhsl);
        //cout << "added " << lhsv << " = " << rhs0v << " ^ " << rhs1v << endl;
    }
}

template <size_t N>
Var Ctx<N>::minputGetInitsAAG (Var initsSW, Step step1)
{
    string zeros = "";
    for (size_t i=0; i<N; i++) zeros += "0";
    Bf_ptr binits = characteristic(zeros, states[step1]);

    Var inits = addBfSW(initsSW, binits);

    return inits;
}

template <size_t N>
Var Ctx<N>::minputGetBadsAAG (Var badsSW, string filename, vector<Var>& aag_to_var_map, Step step1)
{
    ifstream f(filename);
    assert( f );

    string title;
    int maxvar, Ninputs, Nlatches, Noutputs, Nands, output;
    f >> title >> maxvar >> Ninputs >> Nlatches >> Noutputs >> Nands;
    assert( aag_to_var_map.size() == maxvar+1 );

    for (unsigned i=0; i<Ninputs+Nlatches+1; i++)
        f.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
    
    f >> output;
    assert( aag_to_var_map[output >> 1] > 0 );
    Bf_ptr bbads = (output & 1 ? ~v(aag_to_var_map[output >> 1]) :
                                  v(aag_to_var_map[output >> 1]));

    Var bads = addBfSW(badsSW, bbads);

    return bads;
}

// making trans(step1 => step2)
template <size_t N>
Var Ctx<N>::minputGetTransAAG (Var transSW, string filename, vector<Var>& aag_to_var_map, Step step1, Step step2)
{
    ifstream f(filename);
    assert( f );

    string title;
    int maxvar, Ninputs, Nlatches, Noutputs, Nands, output;
    f >> title >> maxvar >> Ninputs >> Nlatches >> Noutputs >> Nands;
    assert( aag_to_var_map.size() == maxvar+1 );

    for (unsigned i=0; i<Ninputs+1; i++)
        f.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
    
    Bf_ptr btrans = v(true);
    for (unsigned i=0, c, n; i<Nlatches; i++)
    {
        f >> c >> n;
        Var x = states[step2]+i, xp = aag_to_var_map[n >> 1];
        assert( xp > 0 );

        Bf_ptr bx = v(x), bxp = (n & 1 ? ~v(xp) : v(xp));
        btrans = btrans & v(addBfSW(fixedSW, bx == bxp));
        //cout << "added " << x << " = " << xp << endl;
    }

    Var trans = addBfSW(transSW, btrans);

    return trans;
}
