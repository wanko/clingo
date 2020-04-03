"""
Test cases for HTc to Clingcon translation
"""

import unittest
from csp.tests import solve_htc


# pylint: disable=missing-docstring, line-too-long

SOL_TAXES = [['lives(mary,germany)', 'lives(paul,germany)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -32000), ('aux(1)', -32000), ('aux(2)', 15000), ('aux(3)', 15000), ('aux(4)', -32000), ('aux(5)', 15000), ('aux(6)', 0), ('aux(7)', 0), ('aux(8)', 15000), ('aux(9)', 32000), ('deduction(mary)', 10000), ('deduction(paul)', 0), ('max', 32000), ('min', 15000), ('rate(mary)', 35), ('rate(paul)', 25), ('tax(mary)', 32000), ('tax(paul)', 15000), ('total(germany)', 47000), ('total(luxemburg)', 0)],
             ['lives(mary,germany)', 'lives(paul,germany)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -31999), ('aux(1)', -31999), ('aux(2)', 15000), ('aux(3)', 15000), ('aux(4)', -31999), ('aux(5)', 15000), ('aux(6)', 0), ('aux(7)', 0), ('aux(8)', 15000), ('aux(9)', 31999), ('deduction(mary)', 10001), ('deduction(paul)', 0), ('max', 31999), ('min', 15000), ('rate(mary)', 35), ('rate(paul)', 25), ('tax(mary)', 31999), ('tax(paul)', 15000), ('total(germany)', 46999), ('total(luxemburg)', 0)],
             ['lives(mary,germany)', 'lives(paul,luxemburg)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -32000), ('aux(1)', -32000), ('aux(2)', 13800), ('aux(3)', 13800), ('aux(4)', -32000), ('aux(5)', 13800), ('aux(6)', 13800), ('aux(7)', 0), ('aux(8)', 0), ('aux(9)', 32000), ('deduction(mary)', 10000), ('deduction(paul)', 0), ('max', 32000), ('min', 13800), ('rate(mary)', 35), ('rate(paul)', 23), ('tax(mary)', 32000), ('tax(paul)', 13800), ('total(germany)', 32000), ('total(luxemburg)', 13800)],
             ['lives(mary,germany)', 'lives(paul,luxemburg)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -31999), ('aux(1)', -31999), ('aux(2)', 13800), ('aux(3)', 13800), ('aux(4)', -31999), ('aux(5)', 13800), ('aux(6)', 13800), ('aux(7)', 0), ('aux(8)', 0), ('aux(9)', 31999), ('deduction(mary)', 10001), ('deduction(paul)', 0), ('max', 31999), ('min', 13800), ('rate(mary)', 35), ('rate(paul)', 23), ('tax(mary)', 31999), ('tax(paul)', 13800), ('total(germany)', 31999), ('total(luxemburg)', 13800)],
             ['lives(mary,luxemburg)', 'lives(paul,germany)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -26000), ('aux(1)', -26000), ('aux(2)', 15000), ('aux(3)', 15000), ('aux(4)', -26000), ('aux(5)', 15000), ('aux(6)', 0), ('aux(7)', 26000), ('aux(8)', 15000), ('aux(9)', 0), ('deduction(mary)', 10000), ('deduction(paul)', 0), ('max', 26000), ('min', 15000), ('rate(mary)', 30), ('rate(paul)', 25), ('tax(mary)', 26000), ('tax(paul)', 15000), ('total(germany)', 15000), ('total(luxemburg)', 26000)],
             ['lives(mary,luxemburg)', 'lives(paul,germany)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -25999), ('aux(1)', -25999), ('aux(2)', 15000), ('aux(3)', 15000), ('aux(4)', -25999), ('aux(5)', 15000), ('aux(6)', 0), ('aux(7)', 25999), ('aux(8)', 15000), ('aux(9)', 0), ('deduction(mary)', 10001), ('deduction(paul)', 0), ('max', 25999), ('min', 15000), ('rate(mary)', 30), ('rate(paul)', 25), ('tax(mary)', 25999), ('tax(paul)', 15000), ('total(germany)', 15000), ('total(luxemburg)', 25999)],
             ['lives(mary,luxemburg)', 'lives(paul,luxemburg)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -26000), ('aux(1)', -26000), ('aux(2)', 13800), ('aux(3)', 13800), ('aux(4)', -26000), ('aux(5)', 13800), ('aux(6)', 13800), ('aux(7)', 26000), ('aux(8)', 0), ('aux(9)', 0), ('deduction(mary)', 10000), ('deduction(paul)', 0), ('max', 26000), ('min', 13800), ('rate(mary)', 30), ('rate(paul)', 23), ('tax(mary)', 26000), ('tax(paul)', 13800), ('total(germany)', 0), ('total(luxemburg)', 39800)],
             ['lives(mary,luxemburg)', 'lives(paul,luxemburg)', 'max_taxes(mary)', 'min_taxes(paul)', ('aux(0)', -25999), ('aux(1)', -25999), ('aux(2)', 13800), ('aux(3)', 13800), ('aux(4)', -25999), ('aux(5)', 13800), ('aux(6)', 13800), ('aux(7)', 25999), ('aux(8)', 0), ('aux(9)', 0), ('deduction(mary)', 10001), ('deduction(paul)', 0), ('max', 25999), ('min', 13800), ('rate(mary)', 30), ('rate(paul)', 23), ('tax(mary)', 25999), ('tax(paul)', 13800), ('total(germany)', 0), ('total(luxemburg)', 39799)]]

class TestMain(unittest.TestCase):
    def test_conditionals(self):
        self.assertEqual(
            solve_htc("""\
            {a}.
            &sum{1:a} = x.
            """, -10, 10),
            [['a', 'def(aux(0))', 'def(x)', ('aux(0)', 1), ('x', 1)],
             ['def(aux(0))', 'def(x)', ('aux(0)', 0), ('x', 0)]])
        self.assertEqual(
            solve_htc("""\
            {a}.
            &sum{1} = x.
            b :- &sum{1:a} < x.
            """, -10, 10),
            [['a', 'def(aux(0))', 'def(x)', ('aux(0)', 1), ('x', 1)],
             ['b', 'def(aux(0))', 'def(x)', ('aux(0)', 0), ('x', 1)]])
        self.assertEqual(
            solve_htc("""\
            &sum{x}=1 :- &sum{ 1 : a }>= 0.
            a :- &sum{x}=1.
            """, -10, 10),
            [])

    def test_assignments(self):
        self.assertEqual(
            solve_htc("""\
            &sum{1} =: x.
            &sum{z} =: y.
            """, -10, 10),
            [['def(x)', ('x', 1), ('y', 0), ('z', 0)]])
        self.assertEqual(
            solve_htc("""\
            {a}.
            &sum{z : a; 1} =: x.
            &sum{x} =: y.
            """, -10, 10),
            [['a', ('aux(0)', 0), ('x', 0), ('y', 0), ('z', 0)],
             ['def(aux(0))', 'def(x)', 'def(y)', ('aux(0)', 0), ('x', 1), ('y', 1), ('z', 0)]])
        self.assertEqual(
            solve_htc("""\
            {a}.
            &sum{1} =: x :- a.
            b :- &sum{x} > 0.
            """, -10, 10),
            [[('x', 0)], ['a', 'b', 'def(x)', ('x', 1)]])
        self.assertEqual(
            solve_htc("""\
            &in{0..2} =: x.
            """, -10, 10),
            [['def(x)', ('x', 0)], ['def(x)', ('x', 1)], ['def(x)', ('x', 2)]])
        self.assertEqual(
            solve_htc("""\
            &in{y..z} =: x.
            """, -10, 10),
            [[('x', 0), ('y', 0), ('z', 0)]])
        self.assertEqual(
            solve_htc("""\
            &sum{z} = 1.
            &sum{y} = 2.
            &in{y..z} =: x.
            """, -10, 10),
            [])
        self.assertEqual(
            solve_htc("""\
            &sum{z} = 2.
            &sum{y} = 1.
            &in{y..z} =: x.
            """, -10, 10),
            [['def(x)', 'def(y)', 'def(z)', ('x', 1), ('y', 1), ('z', 2)],
             ['def(x)', 'def(y)', 'def(z)', ('x', 2), ('y', 1), ('z', 2)]])
        self.assertEqual(
            solve_htc("""\
            {a}.
            &sum{z} = 2 :- a.
            &sum{y} = 1.
            &in{y..z} =: x.
            """, -10, 10),
            [['a', 'def(x)', 'def(y)', 'def(z)', ('x', 1), ('y', 1), ('z', 2)],
             ['a', 'def(x)', 'def(y)', 'def(z)', ('x', 2), ('y', 1), ('z', 2)],
             ['def(y)', ('x', 0), ('y', 1), ('z', 0)]])

    def test_min(self):
        self.assertEqual(
            solve_htc("""\
            &min{3;2;1}=:x.
            """, -10, 10),
            [['def(aux(0))', 'def(x)', ('aux(0)', 1), ('x', 1)]])
        self.assertEqual(
            solve_htc("""\
            &sum{x} = 1.
            a :- &min{3;x} < 2.
            """, -10, 10),
            [['a', 'def(aux(0))', 'def(x)', ('aux(0)', 1), ('x', 1)]])
        self.assertEqual(
            solve_htc("""\
            {a}.
            &min{3;2;1:a}=:x.
            """, -10, 10),
            [['a', 'def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', 1), ('aux(1)', 1), ('x', 1)],
             ['def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', 10), ('aux(1)', 2), ('x', 2)]])
        self.assertEqual(
            solve_htc("""\
            {b}.
            &sum{x} = 1.
            a :- &min{3; x:b} < 2.
            """, -10, 10),
            [['a', 'b', 'def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', 1), ('aux(1)', 1), ('x', 1)],
             ['def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', 10), ('aux(1)', 3), ('x', 1)]])

    def test_max(self):
        self.assertEqual(
            solve_htc("""\
            &max{3;2;1}=:x.
            """, -10, 10),
            [['def(aux(0))', 'def(x)', ('aux(0)', -3), ('x', 3)]])
        self.assertEqual(
            solve_htc("""\
            &sum{x} = 3.
            a :- &max{1;x} > 2.
            """, -10, 10),
            [['a', 'def(aux(0))', 'def(x)', ('aux(0)', -3), ('x', 3)]])
        self.assertEqual(
            solve_htc("""\
            {a}.
            &max{3;2;4:a}=:x.
            """, -10, 10),
            [['a', 'def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', 4), ('aux(1)', -4), ('x', 4)],
             ['def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', -10), ('aux(1)', -3), ('x', 3)]])
        self.assertEqual(
            solve_htc("""\
            {b}.
            &sum{x} = 2.
            a :- &max{1; x:b} <= 1.
            """, -10, 10),
            [['a', 'def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', -10), ('aux(1)', -1), ('x', 2)],
             ['b', 'def(aux(0))', 'def(aux(1))', 'def(x)', ('aux(0)', 2), ('aux(1)', -2), ('x', 2)]])

    def test_taxes(self):
        self.assertEqual(
            solve_htc("""\
            person(paul;mary).
            region(luxemburg;germany).
            rate(germany,  25000, 15).
            rate(germany,  50000, 25).
            rate(germany, 100000, 35).
            rate(luxemburg,  38700, 14).
            rate(luxemburg,  58000, 23).
            rate(luxemburg,  96700, 30).
            income(paul,   60000).
            income(mary,  120000).
            deduction(mary, 10000, 10001).

            1 { lives(P,R) : region(R) } 1 :- person(P).

            &sum{ 0 } =: deduction(P) :- person(P), not deduction(P,_,_).
            &in{ L..H } =: deduction(P) :- deduction(P,L,H).
            &sum{ T } =: rate(P) :- lives(P,R), income(P,I),
                                    T = #max{ T' : rate(R,L,T'), I>=L}.

            &sum{ I*rate(P)-100*deduction(P) } =: 100*tax(P) :- income(P,I).
            &sum{ tax(P) : lives(P,R) } =: total(R) :- region(R).
            &min{ tax(P) : person(P) } =: min.
            &max{ tax(P) : person(P) } =: max.
            min_taxes(P) :- &min{ tax(P') : person(P') } = tax(P), person(P).
            max_taxes(P) :- &max{ tax(P') : person(P') } = tax(P), person(P).

            #show lives/2.
            #show min_taxes/1.
            #show max_taxes/1.
            """, -100000, 100000), SOL_TAXES)
