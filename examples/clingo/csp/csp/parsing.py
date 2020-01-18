"""
This module contains functions for parsing and normalizing constraints.
"""

from functools import reduce
import clingo
from clingo import ast

try:
    from math import gcd
except ImportError:
    def gcd(x, y):
        """
        Calculate the gcd of the given integers.
        """
        x, y = abs(x), abs(y)
        while y:
            x, y = y, x % y
        return x


def match(term, name, arity):
    """
    Match the given term if it is a function with signature `name/arity`.
    """
    return (term.type in (clingo.TheoryTermType.Function, clingo.TheoryTermType.Symbol) and
            term.name == name and
            len(term.arguments) == arity)


def parse_constraints(init):
    """
    Parse and yield sum and diff constraints in the theory data of the given
    `PropagateInit` object.

    Contraints are represented as a triple of a literal, its elements, and an
    upper bound.
    """

    for atom in init.theory_atoms:
        is_sum = match(atom.term, "sum", 1)
        is_diff = match(atom.term, "diff", 1)
        if is_sum or is_diff:
            body = match(atom.term.arguments[0], "body", 0)
            for cons in _parse_constraint(init, atom, is_sum, body):
                yield cons


def _parse_constraint(init, atom, is_sum, strict=False):
    """
    Yield constraints from the given theory atom.

    If `is_sum` is true parses a sum constraint. Otherwise, it parses a
    difference constraint as supported by clingo-dl.

    Contraints are represented as a triple of a literal, its elements, and an
    upper bound.
    """

    elements = []
    rhs = 0

    # map literal
    literal = init.solver_literal(atom.literal)

    # combine coefficients
    seen = {}
    for i, (co, var) in enumerate(_parse_constraint_elems(atom.elements, atom.guard[1], is_sum)):
        if co == 0:
            continue

        if var is None:
            rhs -= co
        elif var not in seen:
            seen[var] = i
            elements.append((co, var))
        else:
            elements[seen[var]][0] += co

    # drop zero weights and divide by gcd
    elements = [(co, var) for co, var in elements if co != 0]
    d = reduce(lambda a, b: gcd(a, b[0]), elements, rhs)
    if d > 1:
        elements = [(co//d, var) for co, var in elements]
        rhs //= d

    for c in _normalize_constraint(init, literal, elements, atom.guard[0], rhs, strict):
        yield c


def _normalize_constraint(init, literal, elements, op, rhs, strict):
    # rerwrite > and < guard
    if op == ">":
        op = ">="
        rhs = rhs + 1
    elif op == "<":
        op = "<="
        rhs -= 1

    # rewrite >= guard
    if op == ">=":
        op = "<="
        rhs = -rhs
        elements = [(-co, var) for co, var in elements]

    if op == "<=":
        if strict and len(elements) == 1:
            yield literal, elements, rhs, True
            return
        yield literal, elements, rhs, False

    elif op == "=":
        if strict:
            if init.assignment.is_true(literal):
                a = b = 1
            else:
                a = init.add_literal()
                b = init.add_literal()

            # Note: this cannot fail because constraint normalization does not propagate
            init.add_clause([-literal, a])
            init.add_clause([-literal, b])
            init.add_clause([-a, -b, literal])
        else:
            a = b = literal

        for c in _normalize_constraint(init, a, elements, "<=", rhs, strict):
            yield c
        for c in _normalize_constraint(init, b, elements, ">=", rhs, strict):
            yield c

        if strict:
            return

    elif op == "!=":
        if strict:
            for c in _normalize_constraint(init, -literal, elements, "=", rhs, True):
                yield c
            return

        a = init.add_literal()
        b = init.add_literal()

        for c in _normalize_constraint(init, a, elements, "<", rhs, False):
            yield c
        for c in _normalize_constraint(init, b, elements, ">", rhs, False):
            yield c

        # Note: this cannot fail
        init.add_clause([a, b, -literal])
        init.add_clause([-a, -b])

    if strict:
        if op == "<=":
            op = ">"
        elif op == "!=":
            op = "="

        for c in _normalize_constraint(init, -literal, elements, op, rhs, False):
            yield c


def _parse_constraint_elems(elems, rhs, is_sum):
    if not is_sum and len(elems) != 1:
        raise RuntimeError("Invalid Syntax")

    for elem in elems:
        if len(elem.terms) == 1 and not elem.condition:
            for co, var in _parse_constraint_elem(elem.terms[0], is_sum):
                yield co, var
        else:
            raise RuntimeError("Invalid Syntax")

    if is_sum:
        for co, var in _parse_constraint_elem(rhs, is_sum):
            yield -co, var
    else:
        term = _evaluate_term(rhs)
        if term.type == clingo.SymbolType.Number:
            yield -term.number, None
        else:
            raise RuntimeError("Invalid Syntax")


def _parse_constraint_elem(term, is_sum):
    if not is_sum:
        if match(term, "-", 2):
            a = _evaluate_term(term.arguments[0])
            if a.type == clingo.SymbolType.Number:
                yield a.number, None
            else:
                yield 1, a

            b = _evaluate_term(term.arguments[1])
            if b.type == clingo.SymbolType.Number:
                yield -b.number, None
            else:
                yield -1, b

        else:
            raise RuntimeError("Invalid Syntax for difference constraint")

    else:
        if match(term, "+", 2):
            for co, var in _parse_constraint_elem(term.arguments[0], True):
                yield co, var
            for co, var in _parse_constraint_elem(term.arguments[1], True):
                yield co, var

        elif match(term, "-", 2):
            for co, var in _parse_constraint_elem(term.arguments[0], True):
                yield co, var
            for co, var in _parse_constraint_elem(term.arguments[1], True):
                yield -co, var

        elif match(term, "*", 2):
            lhs = list(_parse_constraint_elem(term.arguments[0], True))
            for co_prime, var_prime in _parse_constraint_elem(term.arguments[1], True):
                for co, var in lhs:
                    if var is None:
                        yield co*co_prime, var_prime
                    elif var_prime is None:
                        yield co*co_prime, var
                    else:
                        raise RuntimeError("Invalid Syntax, only linear constraints allowed")

        elif match(term, "-", 1):
            for co, var in _parse_constraint_elem(term.arguments[0], True):
                yield -co, var

        elif match(term, "+", 1):
            for co, var in _parse_constraint_elem(term.arguments[0], True):
                yield co, var

        elif term.type == clingo.TheoryTermType.Number:
            yield term.number, None

        elif term.type in (clingo.TheoryTermType.Symbol, clingo.TheoryTermType.Function, clingo.TheoryTermType.Tuple):
            yield 1, _evaluate_term(term)

        else:
            raise RuntimeError("Invalid Syntax for linear constraint")


_BOP = {"+": lambda a, b: a+b,
        "-": lambda a, b: a-b,
        "*": lambda a, b: a*b,
        "**": lambda a, b: a**b,
        "\\": lambda a, b: a%b,
        "/": lambda a, b: a//b}


def _evaluate_term(term):
    # pylint: disable=too-many-return-statements

    # tuples
    if term.type == clingo.TheoryTermType.Tuple:
        return clingo.Tuple(_evaluate_term(x) for x in term.arguments)

    # functions and arithmetic operations
    if term.type == clingo.TheoryTermType.Function:
        # binary operations
        if term.name in _BOP and len(term.arguments) == 2:
            a = _evaluate_term(term.arguments[0])
            b = _evaluate_term(term.arguments[1])

            if a.type != clingo.SymbolType.Number or b.type != clingo.SymbolType.Number:
                raise RuntimeError("Invalid Binary Operation")

            if term.name in ("/", "\\") and b.number == 0:
                raise RuntimeError("Division by Zero")

            return clingo.Number(_BOP[term.name](a.number, b.number))

        # unary operations
        if term.name == "-" and len(term.arguments) == 1:
            a = _evaluate_term(term.arguments[0])

            if a.type == clingo.SymbolType.Number:
                return clingo.Number(-a.number)

            if a.type == clingo.Function and a.name:
                return clingo.Function(a.name, a.arguments, not a.positive)

            raise RuntimeError("Invalid Unary Operation")

        # functions
        return clingo.Function(term.name, (_evaluate_term(x) for x in term.arguments))

    # constants
    if term.type == clingo.TheoryTermType.Symbol:
        return clingo.Function(term.name)

    # numbers
    if term.type == clingo.TheoryTermType.Number:
        return clingo.Number(term.number)

    raise RuntimeError("Invalid Syntax")


class Transformer(object):
    """
    Transforms `clingo.ast.AST` objects by visiting all child nodes.

    Implement `visit_<type>` where `<type>` is the type of the nodes to be
    visited.
    """
    def visit_children(self, x, *args, **kwargs):
        """
        Visit all child nodes of the current node.
        """
        for key in x.child_keys:
            setattr(x, key, self.visit(getattr(x, key), *args, **kwargs))
        return x

    def visit(self, x, *args, **kwargs):
        """
        Default visit method to dispatch calls to child nodes.
        """
        if isinstance(x, ast.AST):
            attr = "visit_" + str(x.type)
            if hasattr(self, attr):
                return getattr(self, attr)(x, *args, **kwargs)
            return self.visit_children(x, *args, **kwargs)
        if isinstance(x, list):
            return [self.visit(y, *args, **kwargs) for y in x]
        if x is None:
            return x
        raise TypeError("unexpected type")


class HeadBodyTransformer(Transformer):
    """
    Transforms sum/diff theory atoms in heads and bodies of rules by turning
    the name of each theory atom into a function with head or body as argument.
    """
    # pylint: disable=invalid-name

    def visit_Rule(self, rule):
        """
        Visit rules adding a parameter indicating whether the head or body is
        being visited.
        """
        rule.head = self.visit(rule.head, loc="head")
        rule.body = self.visit(rule.body, loc="body")
        return rule

    def visit_TheoryAtom(self, atom, loc="body"):
        """
        Modify sum and diff in theory atoms by adding loc as parameter to the
        name of theory atom.
        """
        t = atom.term
        if t.name in ["sum", "diff"] and t.arguments == []:
            atom.term = ast.Function(t.location, t.name, [ast.Function(t.location, loc, [], False)], False)
        return atom


def transform(builder, s):
    """
    Transform the program with csp constraints in the given file and path it to the builder.
    """
    t = HeadBodyTransformer()
    clingo.parse_program(s, lambda stm: builder.add(t.visit(stm)))