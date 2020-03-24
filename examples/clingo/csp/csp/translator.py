import clingo
from csp.astutil import match

AUX = "aux"

class ConstraintAtom(object):
    """
    Representation of a constraint atom.
    """
    def __init__(self, elements, guard, literal, term):
        self.elements = elements
        self.guard = guard
        self.literal = literal
        self.term = term

    def __str__(self):
        return str(self.term) + "{ " + ", ".join([str(element) for element in self.elements]) + " } " + str(self.guard[0])+ " " + str(self.guard[1])

    def __repr__(self):
        return str(self.term) + "{ " + ", ".join([str(element) for element in self.elements]) + " } " + str(self.guard[0])+ " " + str(self.guard[1])


class ConstraintElement(object):
    """
    Tuple of terms.
    """
    def __init__(self, terms, condition, condition_id):
        self.terms = terms
        self.condition = condition
        self.condition_id = condition_id

    def __str__(self):
        condition = ""
        if self.condition:
            condition = " : " + str(self.condition)
        elif self.condition_id:
            condition = " : " + str(self.condition_id)
        return str(self.terms) + condition

    def __repr__(self):
        return str(self)

class ConstraintTerm(object):
    """
    Representation of constraint term.
    """
    def __init__(self, name, number, arguments, arg_type):
        self.name = name
        self.number = number
        self.arguments = arguments
        self.type = arg_type

    def __str__(self):
        arguments = ""
        name = ""
        if self.arguments:
            arguments = "(" + ", ".join([str(term) for term in self.arguments]) + ")"
        if self.type == clingo.TheoryTermType.Number:
            name = str(self.number)
        elif self.type in [clingo.TheoryTermType.Symbol, clingo.TheoryTermType.Function]:
            name = str(self.name)
        return name + arguments

    def __repr__(self):
        return str(self)

HEAD = ConstraintTerm("head", None, [], clingo.TheoryTermType.Symbol)
BODY = ConstraintTerm("body", None, [], clingo.TheoryTermType.Symbol)
ONE = ConstraintTerm(None, 1, None, clingo.TheoryTermType.Number)
ZERO = ConstraintTerm(None, 0, None, clingo.TheoryTermType.Number)
SUM_TERM_HEAD = ConstraintTerm("sum", None, [HEAD], clingo.TheoryTermType.Function)
SUM_TERM_BODY = ConstraintTerm("sum", None, [BODY], clingo.TheoryTermType.Function)

class Translator(object):
    """
    Class that translates ASP program with constraint atoms including assignments and conditionals into a Clingcon program.
    """
    def __init__(self, prg, backend, config):
        self._prg = prg
        self._backend = backend
        self._config = config
        self._defined = {}
        self._auxvars = 0
        self._sum_constraints = set()

    def vars(self, term):
        """
        Return all variables in a term.
        """
        if term.type == clingo.SymbolType.Number:
            return set()
        if match(term, "-", 2) or match(term, "+", 2) or match(term, "*", 2) or match(term, "..", 2):
            return self.vars(term.arguments[0]).union(self.vars(term.arguments[1]))
        if match(term, "-", 1) or match(term, "+", 1):
            return self.vars(term.arguments[0])
        if term.type in (clingo.TheoryTermType.Symbol, clingo.TheoryTermType.Function, clingo.TheoryTermType.Tuple):
            return {term}
        return set()

    def term_to_symbol(self, term):
        """
        Converts theory terms in the form of function symbols to clingo function symbols.
        """
        if term.type == clingo.TheoryTermType.Function:
            return clingo.Function(term.name, [self.term_to_symbol(arg) for arg in term.arguments])
        if term.type == clingo.TheoryTermType.Symbol:
            return clingo.Function(term.name)
        if term.type == clingo.TheoryTermType.Number:
            return clingo.Number(term.number)
        raise RuntimeError("Incorrect Term Type")

    def _add_auxvar(self):
        var = ConstraintTerm(AUX, None, [ConstraintTerm(None, self._auxvars, [], clingo.TheoryTermType.Number)], clingo.TheoryTermType.Function)
        self._auxvars += 1
        return var

    def _add_atom(self, symbol=None):
        with self._backend as backend:
            if symbol:
                return backend.add_atom(symbol)
            return backend.add_atom()

    def _search_atom(self, lit):
        for var in self._defined:
            if lit == self._defined[var]:
                return clingo.Function("def", [self.term_to_symbol(var)])
        for atom in self._sum_constraints:
            if atom.literal == lit:
                return atom
        for atom in self._prg.theory_atoms:
            if atom.literal == lit:
                return atom
        for atom in self._prg.symbolic_atoms:
            if atom.literal == lit:
                return atom.symbol
        return lit

    def _add_rule(self, head, body, choice=False):
        with self._backend as backend:
            backend.add_rule(head, body, choice)
        if self._config.print_trans:
            head_atoms = []
            body_atoms = []
            for lit in head:
                head_atoms.append(str(self._search_atom(lit)))
            for lit in body:
                body_atoms.append(str(self._search_atom(abs(lit))) if lit > 0 else "not "+ str(self._search_atom(abs(lit))))
            lhs, rhs = "", ""
            if choice:
                lhs, rhs = "{", "}"
            head_str = lhs + "; ".join(head_atoms) + rhs
            body_str = ", ".join(body_atoms)
            print(head_str, ":-", body_str, ".")

    def _add_defined(self, var, reason=None):
        if var not in self._defined:
            self._defined[var] = self._add_atom(clingo.Function("def", [self.term_to_symbol(var)]))
        defined_lit = self._defined[var]
        if reason:
            self._add_rule([defined_lit], reason)
        return defined_lit

    def _define_variables(self, atom):
        assert match(atom.term.arguments[0], "head", 0) and match(atom.term, "sum", 1) and not self.conditional(atom)
        for var in self.vars(atom.guard[1]):
            self._add_defined(var, [atom.literal])
        for element in atom.elements:
            reason = [atom.literal]
            for var in self.vars(element.terms[0]):
                if element.condition:
                    reason.append(element.condition_id)
                self._add_defined(var, reason)

    def _fix_undefined(self):
        for var, lit in self._defined.items():
            fix_val = self._add_atom()
            self._sum_constraints.add(ConstraintAtom([ConstraintElement([var], None, None)], ["=", ZERO], fix_val, SUM_TERM_HEAD))
            self._add_rule([fix_val], [-lit])

    def conditional(self, atom):
        """
        Returns true if atom is conditional, false otherwise.
        """
        for element in atom.elements:
            if element.condition or element.condition_id:
                return True
        return False

    def _translate_conditional(self, atom):
        if self._config.print_trans:
            print()
            print("% Translating conditionals:", atom)
            print()
        elements = []
        for element in atom.elements:
            if element.condition_id:
                cond = element.condition_id
                aux_var = self._add_auxvar()
                terms = [aux_var]
                terms.extend(element.terms[1:])
                elements.append(ConstraintElement(terms, None, None))
                self._add_defined(aux_var)
                holds_def = [self._add_defined(var) for var in self.vars(element.terms[0])]
                holds = self._add_atom()
                nholds = self._add_atom()
                aux_var_elem = ConstraintElement([aux_var], None, None)
                holds_term = element.terms[0]
                self._translate_constraint(ConstraintAtom([aux_var_elem], ["=", holds_term], holds, SUM_TERM_HEAD))
                self._translate_constraint(ConstraintAtom([aux_var_elem], ["=", ZERO], nholds, SUM_TERM_HEAD))
                body = [cond]
                body.extend(holds_def)
                self._add_rule([holds], body)

                body = [-cond]
                self._add_rule([nholds], body)

                body = [cond]
                body.append(self._defined[aux_var])
                self._add_rule([holds], body)

                body = [-cond]
                body.append(self._defined[aux_var])
                self._add_rule([nholds], body)

                self._add_rule([cond], [self._defined[aux_var]], True)
            else:
                elements.append(element)
        cond_free_lit = self._add_atom()
        type_term = ConstraintTerm(atom.term.name, None, [HEAD], clingo.TheoryTermType.Function)
        self._translate_constraint(ConstraintAtom(elements, atom.guard, cond_free_lit, type_term))
        self._add_rule([cond_free_lit], [atom.literal])
        #self._add_rule([atom.literal], [cond_free_lit])

    def _translate_assignment(self, atom):
        assert len(self.vars(atom.guard[1])) == 1 and not self.conditional(atom)
        if self._config.print_trans:
            print()
            print("% Translating assignment:", atom)
            print()
        body = [atom.literal]
        for element in atom.elements:
            for var in self.vars(element.terms[0]):
                body.append(self._add_defined(var))
        head_lit = self._add_atom()
        type_term = ConstraintTerm(atom.term.name, None, [HEAD], clingo.TheoryTermType.Function)
        self._translate_constraint(ConstraintAtom(atom.elements, ["=", atom.guard[1]], head_lit, type_term))
        self._add_rule([head_lit], body)

    def _translate_max(self, atom):
        assert not self.conditional(atom)
        if self._config.print_trans:
            print()
            print("% Translating max aggregate:", atom)
            print()
        elements = []
        for element in atom.elements:
            terms = [ConstraintTerm("-", None, [element.terms[0]], clingo.TheoryTermType.Function)]
            for term in element.terms[1:]:
                terms.append(term)
            elements.append(ConstraintElement(terms, element.condition, element.condition_id))
        head_lit = self._add_atom()
        type_term = ConstraintTerm("min", None, [HEAD], clingo.TheoryTermType.Function)
        rhs = ConstraintTerm("-", None, [atom.guard[1]], clingo.TheoryTermType.Function)
        self._translate_constraint(ConstraintAtom(elements, [atom.guard[0], rhs], head_lit, type_term))
        self._add_rule([head_lit], [atom.literal])
        self._add_rule([atom.literal], [head_lit])

    def _translate_min(self, atom):
        assert not self.conditional(atom)
        if self._config.print_trans:
            print()
            print("% Translating min aggregate:", atom)
            print()
        def_elements = []
        alpha_elements = []
        beta_elements = []
        min_var = self._add_auxvar()
        for element in atom.elements:

            # create element that checks for defindness
            body = []
            for var in self.vars(element.terms[0]):
                body.append(self._add_defined(var))
            body.append(atom.literal)
            check_lit = self._add_atom()
            self._add_rule([check_lit], body)
            def_elements.append(ConstraintElement([ONE], None, check_lit))

            # create element that checks if value is strictly smaller than minimum
            check_lit = self._add_atom()
            self._translate_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], [">", element.terms[0]], check_lit, SUM_TERM_BODY))
            alpha_elements.append(ConstraintElement([ONE], None, check_lit))

            # create element that checks if value is greater equal than minimum
            check_lit = self._add_atom()
            self._translate_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], ["=", element.terms[0]], check_lit, SUM_TERM_BODY))
            beta_elements.append(ConstraintElement([ONE], None, check_lit))
        min_def = self._add_defined(min_var)
        def_lit = self._add_atom()
        alpha_lit = self._add_atom()
        beta_lit = self._add_atom()
        eq_lit = self._add_atom()

        self._translate_constraint(ConstraintAtom(def_elements, [">=", ONE], def_lit, SUM_TERM_HEAD))
        self._translate_constraint(ConstraintAtom(alpha_elements, ["=", ZERO], alpha_lit, SUM_TERM_HEAD))
        self._translate_constraint(ConstraintAtom(beta_elements, [">=", ONE], beta_lit, SUM_TERM_HEAD))
        self._translate_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], atom.guard, eq_lit, SUM_TERM_HEAD))
        self._add_rule([def_lit], [min_def, atom.literal])
        self._add_rule([min_def], [def_lit, atom.literal])
        self._add_rule([alpha_lit], [min_def, atom.literal])
        self._add_rule([beta_lit], [min_def, atom.literal])
        self._add_rule([eq_lit], [atom.literal])
        self._add_rule([atom.literal], [eq_lit])

    def _translate_in(self, atom):
        assert not self.conditional(atom) and len(atom.elements) == 1 and atom.guard[0] == "="
        if self._config.print_trans:
            print()
            print("% Translating range assignment:", atom)
            print()
        alpha_term = atom.elements[0].terms[0].arguments[0]
        beta_term = atom.elements[0].terms[0].arguments[1]
        alpha_lit = self._add_atom()
        beta_lit = self._add_atom()
        self._translate_constraint(ConstraintAtom([ConstraintElement([alpha_term], None, None)], ["<=", atom.guard[1]], alpha_lit, SUM_TERM_HEAD))
        self._translate_constraint(ConstraintAtom([ConstraintElement([beta_term], None, None)], [">=", atom.guard[1]], beta_lit, SUM_TERM_HEAD))
        self._add_rule([alpha_lit], [atom.literal])
        self._add_rule([beta_lit], [atom.literal])

    def _add_sum_constraint(self, atom):
        if self._config.print_trans:
            print()
            print("% Adding sum constraint:", atom)
            print()
        self._sum_constraints.add(atom)
        if match(atom.term.arguments[0], "head", 0):
            self._define_variables(atom)
        for element in atom.elements:
            for var in self.vars(element.terms[0]):
                def_lit = self._add_defined(var)
                self._add_rule([], [atom.literal, -def_lit])
        for var in self.vars(atom.guard[1]):
            def_lit = self._add_defined(var)
            self._add_rule([], [atom.literal, -def_lit])

    def _translate_constraint(self, atom):
        if match(atom.term, "sum", 1) and not self.conditional(atom) and atom.guard[0] in ("=", "<", ">", "<=", ">=", "!="):
            self._add_sum_constraint(atom)
        elif self.conditional(atom):
            self._translate_conditional(atom)
        elif atom.guard[0] == "=:":
            self._translate_assignment(atom)
        elif match(atom.term, "max", 1):
            self._translate_max(atom)
        elif match(atom.term, "min", 1):
            self._translate_min(atom)
        elif match(atom.term, "in", 1):
            self._translate_in(atom)

    def _translate_constraints(self):
        for atom in self._prg.theory_atoms:
            self._translate_constraint(atom)

    def translate(self):
        """
        Translates ASP program with constraint atoms including assignments and conditionals into a Clingcon program.
        Adds rules implementing definition of variables, assignments, conditional linear constraint atoms and aggregates count, max and min.
        Returns sum constraints to be added to Clingcon.
        """
        self._translate_constraints()
        self._fix_undefined()
        self._prg.cleanup()
        return self._sum_constraints
