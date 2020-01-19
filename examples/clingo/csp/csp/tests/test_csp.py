"""
Basic tests checking the whole system.
"""

import unittest
from csp.tests import Solver, solve


# pylint: disable=missing-docstring

class TestMain(unittest.TestCase):
    def test_simple(self):
        self.assertEqual(
            solve("""\
            &sum {   1 *y + (-5)*x } <= 0.
            &sum { (-1)*y +   5 *x } <= 0.
            &sum { 15*x } <= 15.
            &sum { 10*x } <= 7.
            """),
            [[('x', -4), ('y', -20)],
             [('x', -3), ('y', -15)],
             [('x', -2), ('y', -10)],
             [('x', -1), ('y', -5)],
             [('x', 0), ('y', 0)]])

        self.assertEqual(
            solve("""\
            &sum {   1 *even + (-2)*_i } <= 0.
            &sum { (-1)*even +   2 *_i } <= 0.
            &sum {   1 *odd + (-2)*_i } <=  1.
            &sum { (-1)*odd +   2 *_i } <= -1.""", -2, 2),
            [[('even', -2), ('odd', -1)],
             [('even', 0), ('odd', 1)]])

        self.assertEqual(
            solve("""\
            a :- &sum{-1*x} <= 0.
            b :- &sum{1*x} <= 5.
            :- not a.
            :- not b."""),
            [['a', 'b', ('x', 0)],
             ['a', 'b', ('x', 1)],
             ['a', 'b', ('x', 2)],
             ['a', 'b', ('x', 3)],
             ['a', 'b', ('x', 4)],
             ['a', 'b', ('x', 5)]])

        self.assertEqual(
            solve("""\
            &sum { 1 * x + (-1) * y } <= -1.
            &sum { 1 * y + (-1) * x } <= -1.
            """), [])

        self.assertEqual(
            solve("""\
            &sum { 1 } <= 2.
            """), [[]])

        self.assertEqual(
            solve("""\
            &sum { 2 } <= 1.
            """), [])

        self.assertEqual(
            solve("""\
            {a}.
            &sum {   1 *x } <= -5 :- a.
            &sum { (-1)*x } <= -5 :- not a.
            """, -6, 6),
            [[('x', 5)],
             [('x', 6)],
             ['a', ('x', -6)],
             ['a', ('x', -5)]])

    def test_parse(self):
        self.assertEqual(solve("&sum { x(f(1+2)) } <= 0.", 0, 0), [[('x(f(3))', 0)]])
        self.assertEqual(solve("&sum { x(f(1-2)) } <= 0.", 0, 0), [[('x(f(-1))', 0)]])
        self.assertEqual(solve("&sum { x(f(-2)) } <= 0.", 0, 0), [[('x(f(-2))', 0)]])
        self.assertEqual(solve("&sum { x(f(2*2)) } <= 0.", 0, 0), [[('x(f(4))', 0)]])
        self.assertEqual(solve("&sum { x(f(4/2)) } <= 0.", 0, 0), [[('x(f(2))', 0)]])
        self.assertEqual(solve("&sum { x(f(9\\2)) } <= 0.", 0, 0), [[('x(f(1))', 0)]])
        self.assertEqual(solve("&sum { (a,b) } <= 0.", 0, 0), [[('(a,b)', 0)]])
        self.assertEqual(solve("&sum { x } = 5."), [[('x', 5)]])
        self.assertEqual(solve("&sum { x } != 0.", -3, 3), [[('x', -3)], [('x', -2)], [('x', -1)], [('x', 1)], [('x', 2)], [('x', 3)]])
        self.assertEqual(solve("&sum { x } < 2.", -3, 3), [[('x', -3)], [('x', -2)], [('x', -1)], [('x', 0)], [('x', 1)]])
        self.assertEqual(solve("&sum { x } > 1.", -3, 3), [[('x', 2)], [('x', 3)]])
        self.assertEqual(solve("&sum { x } >= 1.", -3, 3), [[('x', 1)], [('x', 2)], [('x', 3)]])
        self.assertEqual(solve("a :- &sum { x } >= 1.", -3, 3), [
            [('x', -3)], [('x', -2)], [('x', -1)],
            [('x', 0)],
            ['a', ('x', 1)], ['a', ('x', 2)], ['a', ('x', 3)]])
        self.assertEqual(solve("a :- &sum { x } = 1.", -3, 3), [
            [('x', -3)], [('x', -2)], [('x', -1)],
            [('x', 0)],
            [('x', 2)], [('x', 3)], ['a', ('x', 1)]])
        self.assertEqual(solve("&sum { 5*x + 10*y } = 20.", -3, 3), [[('x', -2), ('y', 3)], [('x', 0), ('y', 2)], [('x', 2), ('y', 1)]])
        self.assertEqual(solve("&sum { -5*x + 10*y } = 20.", -3, 3), [[('x', -2), ('y', 1)], [('x', 0), ('y', 2)], [('x', 2), ('y', 3)]])

    def test_singleton(self):
        self.assertEqual(solve("&sum { x } <= 1.", 0, 2), [[('x', 0)], [('x', 1)]])
        self.assertEqual(solve("&sum { x } >= 1.", 0, 2), [[('x', 1)], [('x', 2)]])
        self.assertEqual(solve("a :- &sum { x } <= 1.", 0, 2), [[('x', 2)], ['a', ('x', 0)], ['a', ('x', 1)]])
        self.assertEqual(solve(":- &sum { x } <= 1.", 0, 2), [[('x', 2)]])
        self.assertEqual(solve(":- not &sum { x } <= 1.", 0, 2), [[('x', 0)], [('x', 1)]])
        self.assertEqual(solve("a :- &sum { x } <= 1. b :- not &sum { x } > 1.", 0, 2), [[('x', 2)], ['a', 'b', ('x', 0)], ['a', 'b', ('x', 1)]])
        self.assertEqual(solve(" :- &sum { x } <= 1. :- not &sum { x } > 1.", 0, 2), [[('x', 2)]])

    def test_distinct(self):
        self.assertEqual(solve("&distinct { x; y }.", 0, 1), [[('x', 0), ('y', 1)], [('x', 1), ('y', 0)]])
        self.assertEqual(solve("&distinct { 2*x; 3*y }.", 2, 3), [[('x', 2), ('y', 2)], [('x', 2), ('y', 3)], [('x', 3), ('y', 3)]])
        self.assertEqual(solve("&distinct { 0*x; 0*y }.", 0, 1), [])
        self.assertEqual(solve("&distinct { 0; 0 }.", 0, 1), [[]])
        self.assertEqual(solve("&distinct { 0; 1 }.", 0, 1), [[]])
        self.assertEqual(solve("&distinct { 2*x; (1+1)*x }.", 0, 1), [[('x', 0)], [('x', 1)]])
        self.assertEqual(solve("&distinct { x; y } :- c. &sum { x } = y :- not c. {c}.", 0, 1), [
            [('x', 0), ('y', 0)],
            [('x', 1), ('y', 1)],
            ['c', ('x', 0), ('y', 1)],
            ['c', ('x', 1), ('y', 0)]])

    def test_multishot(self):
        s = Solver(0, 3)
        self.assertEqual(s.solve("&sum { x } <= 2."), [[('x', 0)], [('x', 1)], [('x', 2)]])
        self.assertEqual(s.solve("&sum { x } <= 1."), [[('x', 0)], [('x', 1)]])
        self.assertEqual(s.solve("&sum { x } <= 0."), [[('x', 0)]])
        self.assertEqual(s.solve("&sum { x } <= 1."), [[('x', 0)]])
        self.assertEqual(s.solve("&sum { x } <= 2."), [[('x', 0)]])
