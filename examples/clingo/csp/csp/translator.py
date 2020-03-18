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

class Translator(object):
    """
    Class that translates ASP program with constraint atoms including assignments and conditionals into a Clingcon program.
    """
    def __init__(self, prg, backend):
        self._prg = prg
        self._backend = backend
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

    def _add_defined(self, var, reason):
        with self._backend as backend:
            if var not in self._defined:
                self._defined[var] = backend.add_atom(clingo.Function("def", [self.term_to_symbol(var)]))
            defined_lit = self._defined[var]
            backend.add_rule([defined_lit], reason)

    def _define_variables(self):
        for atom in self._prg.theory_atoms:
            if match(atom.term.arguments[0], "body", 0):
                continue
            for var in self.vars(atom.guard[1]):
                self._add_defined(var, [atom.literal])
            if atom.guard[0] != "=:":
                for element in atom.elements:
                    reason = [atom.literal]
                    for var in self.vars(element.terms[0]):
                        if element.condition:
                            reason.append(element.condition_id)
                        self._add_defined(var, reason)

    def conditional(self, atom):
        """
        Returns true if atom is conditional, false otherwise.
        """
        for element in atom.elements:
            if element.condition or element.condition_id:
                return True
        return False

    def _translate_conditional(self, atom):
        elements = []
        for element in atom.elements:
            if element.condition_id:
                cond = element.condition_id
                aux_var = self._add_auxvar()
                terms = [aux_var]
                terms.extend(element.terms[1:])
                elements.append(ConstraintElement(terms, None, None))
                with self._backend as backend:
                    holds = backend.add_atom()
                    nholds = backend.add_atom()
                self._add_defined(aux_var, [holds])
                self._add_defined(aux_var, [nholds])
                with self._backend as backend:
                    holds_def = [self._defined[var] for var in self.vars(element.terms[0])]
                    body = [cond]
                    body.extend(holds_def)
                    backend.add_rule([holds], body)

                    body = [-cond]
                    backend.add_rule([nholds], body)

                    body = [cond]
                    body.append(self._defined[aux_var])
                    backend.add_rule([holds], body)

                    body = [-cond]
                    body.append(self._defined[aux_var])
                    backend.add_rule([nholds], body)

                    not_cond = backend.add_atom()
                    backend.add_rule([not_cond], [-cond])
                    backend.add_rule([cond, not_cond], [self._defined[aux_var]])
                aux_var_elem = ConstraintElement([aux_var], None, None)
                holds_term = element.terms[0]
                zero = ConstraintTerm(None, 0, None, clingo.TheoryTermType.Number)
                sum_term = ConstraintTerm("sum", None, [ConstraintTerm("head", None, None, clingo.TheoryTermType.Symbol)], clingo.TheoryTermType.Function)
                self._translate_constraint(ConstraintAtom([aux_var_elem], ["=", holds_term], holds, sum_term))
                self._translate_constraint(ConstraintAtom([aux_var_elem], ["=", zero], nholds, sum_term))
            else:
                elements.append(element)
        with self._backend as backend:
            cond_free_lit = backend.add_atom()
            backend.add_rule([cond_free_lit], [atom.literal])
        type_term = ConstraintTerm(atom.term.name, None, [ConstraintTerm("head", None, None, clingo.TheoryTermType.Symbol)], clingo.TheoryTermType.Function)
        self._translate_constraint(ConstraintAtom(elements, atom.guard, cond_free_lit, type_term))

    def _translate_assignment(self, atom):
        assert len(self.vars(atom.guard[1])) == 1 and not self.conditional(atom)
        body = [atom.literal]
        for element in atom.elements:
            for var in self.vars(element.terms[0]):
                body.append(self._defined[var])
        with self._backend as backend:
            head_lit = backend.add_atom()
            backend.add_rule([head_lit], body)
        type_term = ConstraintTerm(atom.term.name, None, [ConstraintTerm("head", None, None, clingo.TheoryTermType.Symbol)], clingo.TheoryTermType.Function)
        self._translate_constraint(ConstraintAtom(atom.elements, ["=", atom.guard[1]], head_lit, type_term))

    def _translate_max(self, atom):
        assert not self.conditional(atom)
        elements = []
        for element in atom.elements:
            terms = [ConstraintTerm("-", None, [element.terms[0]], clingo.TheoryTermType.Function)]
            for term in element.terms[1:]:
                terms.append(term)
            elements.append(ConstraintElement(terms, element.condition, element.condition_id))
        with self._backend as backend:
            head_lit = backend.add_atom()
            backend.add_rule([head_lit], [atom.literal])
        type_term = ConstraintTerm("min", None, [ConstraintTerm("head", None, None, clingo.TheoryTermType.Symbol)], clingo.TheoryTermType.Function)
        self._translate_constraint(ConstraintAtom(elements, atom.guard, head_lit, type_term))

    def _translate_min(self, atom):
        assert not self.conditional(atom)
        min_var = self._add_auxvar()
        one = ConstraintTerm(None, 1, None, clingo.TheoryTermType.Number)
        zero = ConstraintTerm(None, 0, None, clingo.TheoryTermType.Number)
        sum_term = ConstraintTerm("sum", None, [ConstraintTerm("head", None, None, clingo.TheoryTermType.Symbol)], clingo.TheoryTermType.Function)
        with self._backend as backend:
            def_lit = backend.add_atom()
            alpha_lit = backend.add_atom()
            beta_lit = backend.add_atom()
        self._add_defined(min_var, [def_lit, atom.literal])
        with self._backend as backend:
            backend.add_rule([alpha_lit], [self._defined[min_var]])
            backend.add_rule([beta_lit], [self._defined[min_var]])
            def_elements = []
            alpha_elements = []
            beta_elements = []
            for element in atom.elements:

                # create element that checks for defindness
                body = []
                for var in self.vars(element.terms[0]):
                    body.append(self._defined[var])
                elem_lit = backend.add_atom()
                backend.add_rule([elem_lit], body)
                terms = [one]
                for term in element.terms[1:]:
                    terms.append(term)
                def_elements.append(ConstraintElement(terms, None, elem_lit))

                # create element that checks if value is strictly smaller than minimum
                body = []
                elem_lit = backend.add_atom()
                check_lit = backend.add_atom()
                body.append(check_lit)
                backend.add_rule([elem_lit], body)
                terms = [one]
                for term in element.terms[1:]:
                    terms.append(term)
                alpha_elements.append(ConstraintElement(terms, None, elem_lit))
                self._translate_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], ["<", element.terms[0]], check_lit, sum_term))

                # create element that checks if value is greater equal than minimum
                body = []
                elem_lit = backend.add_atom()
                check_lit = backend.add_atom()
                body.append(check_lit)
                backend.add_rule([elem_lit], body)
                terms = [one]
                for term in element.terms[1:]:
                    terms.append(term)
                beta_elements.append(ConstraintElement(terms, None, elem_lit))
                self._translate_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], ["<=", element.terms[0]], check_lit, sum_term))

        self._translate_constraint(ConstraintAtom(def_elements, [">=", one], def_lit, sum_term))
        self._translate_constraint(ConstraintAtom(alpha_elements, ["<=", zero], alpha_lit, sum_term))
        self._translate_constraint(ConstraintAtom(beta_elements, [">=", one], beta_lit, sum_term))

    def _translate_in(self, atom):
        assert not self.conditional(atom) and len(atom.elements) == 1 and atom.guard[0] == "="
        sum_term = ConstraintTerm("sum", None, [ConstraintTerm("head", None, None, clingo.TheoryTermType.Symbol)], clingo.TheoryTermType.Function)
        alpha_term = atom.elements[0].terms[0].arguments[0]
        beta_term = atom.elements[0].terms[0].arguments[1]
        with self._backend as backend:
            alpha_lit = backend.add_atom()
            beta_lit = backend.add_atom()
            backend.add_rule([alpha_lit], [atom.literal])
            backend.add_rule([beta_lit], [atom.literal])
        self._translate_constraint(ConstraintAtom([ConstraintElement([alpha_term], None, None)], [">=", atom.guard[1]], alpha_lit, sum_term))
        self._translate_constraint(ConstraintAtom([ConstraintElement([beta_term], None, None)], ["<=", atom.guard[1]], beta_lit, sum_term))

    def _translate_constraint(self, atom):
        if self.conditional(atom):
            self._translate_conditional(atom)
        elif atom.guard[0] == "=:":
            self._translate_assignment(atom)
        elif match(atom.term, "max", 1):
            self._translate_max(atom)
        elif match(atom.term, "min", 1):
            self._translate_min(atom)
        elif match(atom.term, "in", 1):
            self._translate_in(atom)
        elif match(atom.term, "sum", 1) and not self.conditional(atom):
            self._sum_constraints.add(atom)

    def _translate_constraints(self):
        for atom in self._prg.theory_atoms:
            self._translate_constraint(atom)

    def translate(self):
        """
        Translates ASP program with constraint atoms including assignments and conditionals into a Clingcon program.
        Adds rules implementing definition of variables, assignments, conditional linear constraint atoms and aggregates count, max and min.
        Returns sum constraints to be added to Clingcon.
        """
        self._define_variables()
        self._translate_constraints()
        return self._sum_constraints
