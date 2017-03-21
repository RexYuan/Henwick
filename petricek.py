"""
Synthesize a loop invariant expression for Tomas Petricek's
example program retrieved from http://stackoverflow.com/a/3221583/2448540
"""

# Program:
# j = 9;
# i = 0;
# while (i < 10)
# {
#     i = i + 1;
#     j = j - 1;
# }

# Goal:
# Given program pre-condition = (| T |)
# and post-condition = (| i = 10 and j = -1 |),
# Find invariant = (| i + j == 9 and i < 11 |).

# Proof:
# (| T |)
# (| eta[j/9][i/0] |) Implied
#   i = 0;
# (| eta[j/9] |) Assignment
#   j = 9;
# (| eta |) Assignment
#   while (i < 10)
#   {
#     (| eta and i < 10|)
#     (| eta[j/j-1][i/i+1] |) Implied
#       i = i + 1;
#     (| eta[j/j-1] |) Assignment
#       j = j - 1;
#     (| eta |) Assignment
#   }
# (| eta and not i < 10 |) While
# (| i = 10 and j = -1 |) Implied

# Requirements:
# Given an eta,
# prove the validity of these three implications:
# 1) T => eta[j/9][i/0]
# 2) eta and not i < 10 => i = 10 and j = -1
# 3) i < 10 and eta => eta[j-1/j][i+1/i]

# Strategy:
# 1) Prune with logical requirements for invariant.
# Given an expression E for eta, for any failure in checking some requirements R,
# SMT solver Z3 would return a particular model M (valuation), that makes R, with
# eta substituted with E, evaluate to false, when the variables in eta are
# substituted with the corresponding concrete values in M.
# Thus, we can examine the form of R and devise pruning strategies from the fact
# that M resolves much of R but the part of eta, where it can only be checked
# after substituting with some expression E. So, with the knowledge of the form
# of R and how everything but eta in R evaluates to under M, we need only to check
# what E evaluates to under M to determine if R holds or not.
# For requirement 1), T => eta[j/9][i/0], since eta is in the concequent slot of
# an implication, and under any valuation T evaluates to True, if eta[j/9][i/0]
# evaluates to False under M, this should be pruned.
# For requirement 2), eta and not i < 10 => i = 10 and j = -1, if we know from Z3
# that, for an expression E1 and model M, this requirement is False, we know that
# , under M, E1 and not i < 10 evaluates to True and i = 10 and j = -1 to False.
# So, for an expression E2, we need only to check whether E2 evaluates to True
# under M to decide if this should be pruned, and thus saving time asking Z3.
# For i < 10 and eta => eta[j-1/j][i+1/i], if i < 10 and E1 => E1[j-1/j][i+1/i]
# evaluates to False under M, E1 must evaluates to True and E1[j-1/j][i+1/i] to
# False, respectively, under M. So, we only need to check if E2 is True and
# E2[j-1/j][i+1/i] is False to prune it off.
# 2) NOTE: how to Prune with semantic requirements.
# simplify to true or false
# 3) NOTE: Prune with history or semantic equivalence like commutativity
# 4) NOTE: invariant insight
# 5) NOTE: depth limited on offsprings count

# grammar:
# S    ::= Bool
# Bool ::= And(Bool, Bool) | Or(Bool, Bool) | Implies(Bool, Bool) |
#          Int > Int | Int >= Int | Int == Int
# Int  ::= Term | Term + Term | Term - Term
# Term ::= Cst | Var
# Cst  ::= -1 | 9 | 10 | 11
# Var  ::= i | j

from z3 import *
from time import time

class Z3:
    def __init__(self):
        NT = DeclareSort('Nonterminal')
        self._S     = Bool('S')
        self._Bool1 = Bool('Bool1')
        self._Bool2 = Bool('Bool2')
        self._Bool3 = Bool('Bool3')
        self._Bool4 = Bool('Bool4')
        self._Bool5 = Bool('Bool5')
        self._Bool6 = Bool('Bool6')
        self._Bool7 = Bool('Bool7')
        self._Bool8 = Bool('Bool8')
        self._Bool9 = Bool('Bool9')
        self._Bool10 = Bool('Bool10')
        self._Bool11 = Bool('Bool11')
        self._Bool12 = Bool('Bool12')
        self._Bool13 = Bool('Bool13')
        self._Bool14 = Bool('Bool14')

        self._Int1  = Int('Int1')
        self._Int2  = Int('Int2')
        self._Int3  = Int('Int3')
        self._Int4  = Int('Int4')
        self._Int5  = Int('Int5')
        self._Int6  = Int('Int6')
        self._Int7  = Int('Int7')
        self._Int8  = Int('Int8')
        self._Int9  = Int('Int9')
        self._Int10  = Int('Int10')
        self._Int11  = Int('Int11')
        self._Int12  = Int('Int12')
        self._Int13  = Int('Int13')
        self._Int14  = Int('Int14')
        self._Int15  = Int('Int15')
        self._Int16  = Int('Int16')
        self._Int17  = Int('Int17')
        self._Int18  = Int('Int18')
        self._Int19  = Int('Int19')
        self._Int20  = Int('Int20')
        self._Int21  = Int('Int21')
        self._Int22  = Int('Int22')
        self._Int23  = Int('Int23')
        self._Int24  = Int('Int24')
        self._Int25  = Int('Int25')
        self._Int26  = Int('Int26')
        self._Int27  = Int('Int27')
        self._Int28  = Int('Int28')
        self._Int29  = Int('Int29')
        self._Int30  = Int('Int30')
        self._Int31  = Int('Int31')
        self._Int32  = Int('Int32')
        self._Int33  = Int('Int33')
        self._Int34  = Int('Int34')
        self._Int35  = Int('Int35')
        self._Int36  = Int('Int36')
        self._Int37  = Int('Int37')
        self._Int38  = Int('Int38')
        self._Int39  = Int('Int39')
        self._Int40  = Int('Int40')
        self._Int41  = Int('Int41')
        self._Int42  = Int('Int42')
        self._Int43  = Int('Int43')
        self._Int44  = Int('Int44')
        self._Int45  = Int('Int45')
        self._Int46  = Int('Int46')
        self._Int47  = Int('Int47')
        self._Int48  = Int('Int48')
        self._Int49  = Int('Int49')
        self._Int50  = Int('Int50')
        self._Int51  = Int('Int51')
        self._Int52  = Int('Int52')
        self._Int53  = Int('Int53')
        self._Int54  = Int('Int54')
        self._Int55  = Int('Int55')
        self._Int56  = Int('Int56')
        self._Int57  = Int('Int57')
        self._Int58  = Int('Int58')
        self._Int59  = Int('Int59')
        self._Int60  = Int('Int60')

        self._Num1 = Int('Num1')
        self._Num2 = Int('Num2')
        self._Num3 = Int('Num3')
        self._Num4 = Int('Num4')
        self._Num5 = Int('Num5')
        self._Num6 = Int('Num6')
        self._Num7 = Int('Num7')
        self._Num8 = Int('Num8')
        self._Num9 = Int('Num9')
        self._Num10 = Int('Num10')
        self._Num11 = Int('Num11')
        self._Num12 = Int('Num12')
        self._Num13 = Int('Num13')
        self._Num14 = Int('Num14')
        self._Num15 = Int('Num15')
        self._Num16 = Int('Num16')
        self._Num17 = Int('Num17')
        self._Num18 = Int('Num18')
        self._Num19 = Int('Num19')
        self._Num20 = Int('Num20')
        self._Num21 = Int('Num21')
        self._Num22 = Int('Num22')
        self._Num23 = Int('Num23')
        self._Num24 = Int('Num24')
        self._Num25 = Int('Num25')
        self._Num26 = Int('Num26')
        self._Num27 = Int('Num27')
        self._Num28 = Int('Num28')
        self._Num29 = Int('Num29')
        self._Num30 = Int('Num30')
        self._Num31 = Int('Num31')
        self._Num32 = Int('Num32')
        self._Num33 = Int('Num33')
        self._Num34 = Int('Num34')
        self._Num35 = Int('Num35')
        self._Num36 = Int('Num36')
        self._Num37 = Int('Num37')
        self._Num38 = Int('Num38')
        self._Num39 = Int('Num39')
        self._Num40 = Int('Num40')
        self._Num41 = Int('Num41')
        self._Num42 = Int('Num42')
        self._Num43 = Int('Num43')
        self._Num44 = Int('Num44')
        self._Num45 = Int('Num45')
        self._Num46 = Int('Num46')
        self._Num47 = Int('Num47')
        self._Num48 = Int('Num48')
        self._Num49 = Int('Num49')
        self._Num50 = Int('Num50')
        self._Num51 = Int('Num51')
        self._Num52 = Int('Num52')
        self._Num53 = Int('Num53')
        self._Num54 = Int('Num54')
        self._Num55 = Int('Num55')
        self._Num56 = Int('Num56')
        self._Num57 = Int('Num57')
        self._Num58 = Int('Num58')
        self._Num59 = Int('Num59')
        self._Num60 = Int('Num60')
        self._Num61 = Int('Num61')
        self._Num62 = Int('Num62')
        self._Num63 = Int('Num63')
        self._Num64 = Int('Num64')
        self._Num65 = Int('Num65')
        self._Num66 = Int('Num66')
        self._Num67 = Int('Num67')
        self._Num68 = Int('Num68')
        self._Num69 = Int('Num69')
        self._Num70 = Int('Num70')
        self._Num71 = Int('Num71')
        self._Num72 = Int('Num72')
        self._Num73 = Int('Num73')
        self._Num74 = Int('Num74')
        self._Num75 = Int('Num75')
        self._Num76 = Int('Num76')
        self._Num77 = Int('Num77')
        self._Num78 = Int('Num78')
        self._Num79 = Int('Num79')
        self._Num80 = Int('Num80')
        self._Num81 = Int('Num81')
        self._Num82 = Int('Num82')
        self._Num83 = Int('Num83')
        self._Num84 = Int('Num84')
        self._Num85 = Int('Num85')
        self._Num86 = Int('Num86')
        self._Num87 = Int('Num87')
        self._Num88 = Int('Num88')
        self._Num89 = Int('Num89')
        self._Num90 = Int('Num90')
        self._Num91 = Int('Num91')
        self._Num92 = Int('Num92')
        self._Num93 = Int('Num93')
        self._Num94 = Int('Num94')
        self._Num95 = Int('Num95')
        self._Num96 = Int('Num96')
        self._Num97 = Int('Num97')
        self._Num98 = Int('Num98')
        self._Num99 = Int('Num99')
        self._Num100 = Int('Num100')
        self._Num101 = Int('Num101')
        self._Num102 = Int('Num102')
        self._Num103 = Int('Num103')
        self._Num104 = Int('Num104')
        self._Num105 = Int('Num105')
        self._Num106 = Int('Num106')
        self._Num107 = Int('Num107')
        self._Num108 = Int('Num108')
        self._Num109 = Int('Num109')
        self._Num110 = Int('Num110')
        self._Num111 = Int('Num111')
        self._Num112 = Int('Num112')
        self._Num113 = Int('Num113')
        self._Num114 = Int('Num114')
        self._Num115 = Int('Num115')
        self._Num116 = Int('Num116')
        self._Num117 = Int('Num117')
        self._Num118 = Int('Num118')
        self._Num119 = Int('Num119')
        self._Num120 = Int('Num120')
        self._Num121 = Int('Num121')
        self._Num122 = Int('Num122')
        self._Num123 = Int('Num123')
        self._Num124 = Int('Num124')
        self._Num125 = Int('Num125')
        self._Num126 = Int('Num126')
        self._Num127 = Int('Num127')
        self._Num128 = Int('Num128')
        self._Num129 = Int('Num129')
        self._Num130 = Int('Num130')
        self._Num131 = Int('Num131')
        self._Num132 = Int('Num132')
        self._Num133 = Int('Num133')
        self._Num134 = Int('Num134')
        self._Num135 = Int('Num135')
        self._Num136 = Int('Num136')
        self._Num137 = Int('Num137')
        self._Num138 = Int('Num138')
        self._Num139 = Int('Num139')
        self._Num140 = Int('Num140')
        self._Num141 = Int('Num141')
        self._Num142 = Int('Num142')
        self._Num143 = Int('Num143')
        self._Num144 = Int('Num144')
        self._Num145 = Int('Num145')
        self._Num146 = Int('Num146')
        self._Num147 = Int('Num147')
        self._Num148 = Int('Num148')
        self._Num149 = Int('Num149')
        self._Num150 = Int('Num150')
        self._Num151 = Int('Num151')
        self._Num152 = Int('Num152')
        self._Num153 = Int('Num153')
        self._Num154 = Int('Num154')
        self._Num155 = Int('Num155')
        self._Num156 = Int('Num156')
        self._Num157 = Int('Num157')
        self._Num158 = Int('Num158')
        self._Num159 = Int('Num159')
        self._Num160 = Int('Num160')
        self._Num161 = Int('Num161')
        self._Num162 = Int('Num162')
        self._Num163 = Int('Num163')
        self._Num164 = Int('Num164')
        self._Num165 = Int('Num165')
        self._Num166 = Int('Num166')
        self._Num167 = Int('Num167')
        self._Num168 = Int('Num168')
        self._Num169 = Int('Num169')
        self._Num170 = Int('Num170')
        self._Num171 = Int('Num171')
        self._Num172 = Int('Num172')
        self._Num173 = Int('Num173')
        self._Num174 = Int('Num174')
        self._Num175 = Int('Num175')
        self._Num176 = Int('Num176')
        self._Num177 = Int('Num177')
        self._Num178 = Int('Num178')
        self._Num179 = Int('Num179')
        self._Num180 = Int('Num180')

        self._Cst   = Int('Cst')
        self._Var   = Int('Var')
        self.i      = Int('i')
        self.j      = Int('j')
        """
        self._Bool1: [And(self._Bool1, self._Bool2),
                      self._Int1 == self._Int2,
                      self._Int1 > self._Int2,
                      Or(self._Bool1, self._Bool2),
                      Implies(self._Bool1, self._Bool2),
                      self._Int1 >= self._Int2],
        self._Bool2: [And(self._Bool1, self._Bool2),
                      self._Int1 == self._Int2,
                      self._Int1 > self._Int2,
                      Or(self._Bool1, self._Bool2),
                      Implies(self._Bool1, self._Bool2),
                      self._Int1 >= self._Int2,],
        """
        self.prod = {
            self._S:     [And(self._Bool1, self._Bool2)],
                          #self._Int1 == self._Int2,
                          #self._Int3 > self._Int4
            self._Bool1: [#And(self._Bool3, self._Bool4),
            self._Int7 < self._Int8,
                          self._Int5 == self._Int6
                          ],
            self._Bool2: [#And(self._Bool5, self._Bool6),
            self._Int9 == self._Int10,
                          self._Int11 < self._Int12
                          ],
            self._Bool3: [And(self._Bool7, self._Bool8),
                          self._Int13 == self._Int14,
                          self._Int15 > self._Int16],
            self._Bool4: [And(self._Bool9, self._Bool10),
                          self._Int17 == self._Int18,
                          self._Int19 > self._Int20],
            self._Bool5: [And(self._Bool11, self._Bool12),
                          self._Int21 == self._Int22,
                          self._Int24 > self._Int23],
            self._Bool6: [And(self._Bool13, self._Bool14),
                          self._Int25 == self._Int26,
                          self._Int27 > self._Int28],
            self._Bool7: [self._Int29 == self._Int30,
                          self._Int31 > self._Int32],
            self._Bool8: [self._Int33 == self._Int34,
                          self._Int35 > self._Int36],
            self._Bool9: [self._Int37 == self._Int38,
                          self._Int39 > self._Int40],
            self._Bool10: [self._Int41 == self._Int42,
                          self._Int43 > self._Int44],
            self._Bool11: [self._Int45 == self._Int46,
                          self._Int47 > self._Int48],
            self._Bool12: [self._Int49 == self._Int50,
                          self._Int51 > self._Int52],
            self._Bool13: [self._Int53 == self._Int54,
                          self._Int55 > self._Int56],
            self._Bool14: [self._Int57 == self._Int58,
                          self._Int59 > self._Int60],


            self._Int1:  [self._Num1,
                          self._Num2 + self._Num3],
            self._Int2:  [self._Num4,
                          self._Num5 + self._Num6],
            self._Int3:  [self._Num7,
                          self._Num8 + self._Num9],
            self._Int4:  [self._Num10,
                          self._Num11 + self._Num12],
            self._Int5:  [self._Num13,
                          self._Num14 + self._Num15],
            self._Int6:  [self._Num16,
                          self._Num17 + self._Num18],
            self._Int7:  [self._Num19,
                          self._Num20 + self._Num21],
            self._Int8:  [self._Num22,
                          self._Num23 + self._Num24],
            self._Int9:  [self._Num25,
                          self._Num26 + self._Num27],
            self._Int10:  [self._Num28,
                          self._Num29 + self._Num30],
            self._Int11:  [self._Num31,
                          self._Num32 + self._Num33],
            self._Int12:  [self._Num34,
                          self._Num35 + self._Num36],
            self._Int13:  [self._Num37,
                          self._Num38 + self._Num39],
            self._Int14:  [self._Num40,
                          self._Num41 + self._Num42],
            self._Int15:  [self._Num43,
                          self._Num44 + self._Num45],
            self._Int16:  [self._Num46,
                          self._Num47 + self._Num48],
            self._Int17:  [self._Num49,
                          self._Num50 + self._Num51],
            self._Int18:  [self._Num52,
                          self._Num53 + self._Num54],
            self._Int19:  [self._Num55,
                          self._Num56 + self._Num57],
            self._Int20:  [self._Num58,
                          self._Num59 + self._Num60],
            self._Int21:  [self._Num61,
                          self._Num62 + self._Num63],
            self._Int22:  [self._Num64,
                          self._Num65 + self._Num66],
            self._Int23:  [self._Num67,
                          self._Num68 + self._Num69],
            self._Int24:  [self._Num70,
                          self._Num71 + self._Num72],
            self._Int25:  [self._Num73,
                          self._Num74 + self._Num75],
            self._Int26:  [self._Num76,
                          self._Num77 + self._Num78],
            self._Int27:  [self._Num79,
                          self._Num80 + self._Num81],
            self._Int28:  [self._Num82,
                          self._Num83 + self._Num84],
            self._Int29:  [self._Num85,
                          self._Num86 + self._Num87],
            self._Int30:  [self._Num88,
                          self._Num89 + self._Num90],
            self._Int31:  [self._Num91,
                          self._Num92 + self._Num93],
            self._Int32:  [self._Num94,
                          self._Num95 + self._Num96],
            self._Int33:  [self._Num97,
                          self._Num98 + self._Num99],
            self._Int34:  [self._Num100,
                          self._Num101 + self._Num102],
            self._Int35:  [self._Num103,
                          self._Num104 + self._Num105],
            self._Int36:  [self._Num106,
                          self._Num107 + self._Num108],
            self._Int37:  [self._Num109,
                          self._Num110 + self._Num111],
            self._Int38:  [self._Num112,
                          self._Num113 + self._Num114],
            self._Int39:  [self._Num115,
                          self._Num116 + self._Num117],
            self._Int40:  [self._Num118,
                          self._Num119 + self._Num120],
            self._Int41:  [self._Num121,
                          self._Num122 + self._Num123],
            self._Int42:  [self._Num124,
                          self._Num125 + self._Num126],
            self._Int43:  [self._Num127,
                          self._Num128 + self._Num129],
            self._Int44:  [self._Num130,
                          self._Num131 + self._Num132],
            self._Int45:  [self._Num133,
                          self._Num134 + self._Num135],
            self._Int46:  [self._Num136,
                          self._Num137 + self._Num138],
            self._Int47:  [self._Num139,
                          self._Num140 + self._Num141],
            self._Int48:  [self._Num142,
                          self._Num143 + self._Num144],
            self._Int49:  [self._Num145,
                          self._Num146 + self._Num147],
            self._Int50:  [self._Num148,
                          self._Num149 + self._Num150],
            self._Int51:  [self._Num151,
                          self._Num152 + self._Num153],
            self._Int52:  [self._Num154,
                          self._Num155 + self._Num156],
            self._Int53:  [self._Num157,
                          self._Num158 + self._Num159],
            self._Int54:  [self._Num160,
                          self._Num161 + self._Num162],
            self._Int55:  [self._Num163,
                          self._Num164 + self._Num165],
            self._Int56:  [self._Num166,
                          self._Num167 + self._Num168],
            self._Int57:  [self._Num169,
                          self._Num170 + self._Num171],
            self._Int58:  [self._Num172,
                          self._Num173 + self._Num174],
            self._Int59:  [self._Num175,
                          self._Num176 + self._Num177],
            self._Int60:  [self._Num178,
                          self._Num179 + self._Num180],


            self._Num1:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num2:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num3:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num4:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num5:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num6:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num7:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num8:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num9:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num10:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num11:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num12:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num13:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num14:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num15:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num16:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num17:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num18:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num19:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num20:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num21:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num22:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num23:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num24:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num25:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num26:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num27:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num28:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num29:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num30:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num31:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num32:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num33:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num34:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num35:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num36:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num37:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num38:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num39:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num40:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num41:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num42:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num43:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num44:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num45:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num46:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num47:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num48:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num49:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num50:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num51:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num52:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num53:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num54:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num55:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num56:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num57:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num58:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num59:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num60:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num61:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num62:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num63:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num64:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num65:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num66:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num67:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num68:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num69:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num70:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num71:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num72:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num73:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num74:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num75:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num76:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num77:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num78:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num79:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num80:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num81:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num82:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num83:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num84:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num85:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num86:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num87:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num88:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num89:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num90:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num91:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num92:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num93:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num94:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num95:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num96:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num97:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num98:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num99:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num100:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num101:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num102:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num103:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num104:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num105:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num106:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num107:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num108:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num109:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num110:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num111:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num112:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num113:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num114:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num115:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num116:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num117:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num118:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num119:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num120:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num121:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num122:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num123:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num124:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num125:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num126:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num127:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num128:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num129:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num130:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num131:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num132:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num133:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num134:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num135:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num136:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num137:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num138:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num139:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num140:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num141:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num142:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num143:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num144:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num145:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num146:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num147:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num148:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num149:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num150:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num151:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num152:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num153:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num154:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num155:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num156:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num157:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num158:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num159:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num160:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num161:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num162:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num163:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num164:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num165:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num166:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num167:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num168:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num169:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num170:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num171:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num172:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num173:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num174:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num175:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num176:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num177:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num178:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num179:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Num180:  [self.i, self.j, IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],

            self._Cst:   [IntVal(-1), IntVal(9), IntVal(10), IntVal(11)],
            self._Var:   [self.i, self.j]

        }
        self.solver = Solver()
        self.counter_examples1 = []
        self.counter_examples2 = []
        self.counter_examples3 = []
        self.history = []
        self.query_counter = 0
        self.pruneh_counter = 0
        self.prune1_counter = 0
        self.prune2_counter = 0
        self.prune3_counter = 0

    def isImpValid(self, imp):
        self.solver.push()
        self.solver.add(Not(imp))
        result = self.solver.check()
        ret = True if result == unsat else self.solver.model()
        self.solver.pop()
        return ret

    def checkEta(self, eta):
        # req 1) T => eta[j/9][i/0]
        result = self.isImpValid(Implies(True, substitute(eta, (self.j, IntVal(9)), (self.i, IntVal(0)))))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples1.append((result[self.i], result[self.j]))
            return False
        # req 2) eta and not i < 10 => i = 10 and j = -1
        result = self.isImpValid(Implies(And(eta, Not(self.i < IntVal(10))), And(self.i == IntVal(10), self.j == IntVal(-1))))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples2.append((result[self.i], result[self.j]))
            return False
        # req 3) i < 10 and eta => eta[j-1/j][i+1/i]
        result = self.isImpValid(Implies(And(self.i < IntVal(10), eta), substitute(eta, (self.j, self.j-IntVal(1)), (self.i, self.i+IntVal(1)))))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples3.append((result[self.i], result[self.j]))
            return False
        return True

    def pruned(self, exp):
        # NOTE strat 2)
        """if simplify(exp) == True or simplify(exp) == False:
            return True
        if simplify(exp) in self.history:
            return True
        self.history.append(simplify(exp))
        """
        # pruning with counter examples
        # T => eta[j/9][i/0]
        #if any(simplify(substitute(substitute(exp, (self.j, IntVal(9)), (self.i, IntVal(0))),
        #       (self.i, ci), (self.j, cj))) == False
        #       for (ci, cj) in self.counter_examples1):"""
        if simplify(substitute(exp, (self.j, IntVal(9)), (self.i, IntVal(0)))) == False:
            self.prune1_counter += 1
            return True
        # eta and not i < 10 => i = 10 and j = -1
        if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
               for (ci, cj) in self.counter_examples2):
            self.prune2_counter += 1
            return True
        # i < 10 and eta => eta[j-1/j][i+1/i]
        #if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
        #       and simplify(substitute(substitute(exp, (self.j, self.j-IntVal(1)), (self.i, self.i+IntVal(1))),
        #       (self.i, ci), (self.j, cj))) for (ci, cj) in self.counter_examples3):
        if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
               and simplify(substitute(exp, (self.j, cj-IntVal(1)),
                                            (self.i, ci+IntVal(1)))) == False
               for (ci, cj) in self.counter_examples3):
            self.prune3_counter += 1
            return True

    def getConstituents(self, exp):
        for c in exp.children():
            if c.children():
                yield from self.getConstituents(c)
            else:
                yield c

    def genesis(self, exp, limit):
        print(exp)
        if simplify(exp) == True or simplify(exp) == False:
            return False
        """if simplify(exp) in self.history:
            return False
        self.history.append(simplify(exp))
        """
        offsprings = list(self.getConstituents(exp))
        children = exp.children()
        # depth limited search
        if len(offsprings) > limit:
            return False
        # recursion base
        # if expression has children and they're all termini or
        # if expression has no child and is a terminus
        if (children and not any(c in self.prod for c in offsprings) or
            not children and exp not in self.prod):
            # pruning
            if self.pruned(exp):
                return False
            # query SMT solver
            self.query_counter+=1
            if self.checkEta(exp):
                return exp
            else:
                return False
        # expression expansion
        # NOTE: search strat? how to find insight for goal from other things?
        #       such as post like said from textbook? or anyway get some general
        #       progenitive direction from context? like changning grammar on the fly
        #       or pruning off symmetric function application such as "And, Or"
        #       when args are semantically equivalent in the sense that their
        #       production rules are the same?
        #       I should go back and read more about classic AI search for insight
        # single term
        if not offsprings:
            for p in self.prod[exp]:
                ret = self.genesis(p, limit)
                # eta is found
                if type(ret) == BoolRef:
                    return ret
        # multiple terms
        else:
            for c in [c for c in offsprings if c in self.prod]:
                for p in self.prod[c]:
                    ret = self.genesis(substitute(exp, (c, p)), limit)
                    # eta is found
                    if type(ret) == BoolRef:
                        return ret
        return False

    def synthesis(self, limit):
        # iterative deepening search
        for l in range(5, limit+1):
            result = self.genesis(self._S, l)
            print(l)
            self.report()
            # eta is found
            if type(result) == BoolRef:
                return result

    def test(self):
        print(self.checkEta(self.i+self.j==IntVal(9)))
        print(self.checkEta(And(self.i+self.j==IntVal(9), self.i < IntVal(11))))
        return

    def report(self):
        # stats
        print("z3 queried:", z3.query_counter, "\n")
        print("history size:", len(self.history))
        print("history pruned:", z3.pruneh_counter, "\n")
        print("ce 1 size:", len(self.counter_examples1))
        print("req 1 pruned:", z3.prune1_counter, "\n")
        print("ce 2 size:", len(self.counter_examples2))
        print("req 2 pruned:", z3.prune2_counter, "\n")
        print("ce 3 size:", len(self.counter_examples3))
        print("req 3 pruned:", z3.prune3_counter, "\n")
        return

z3 = Z3()
t = time()
print(z3.synthesis(10))
z3.report()
print("time:", time()-t)

#z3.test()
