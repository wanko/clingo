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
        return "&"+str(self.term) + "{ " + "; ".join([str(element) for element in self.elements]) + " } " + str(self.guard[0])+ " " + str(self.guard[1])

    def __repr__(self):
        return str(self)

    @staticmethod
    def copy(atom):
        """
        Copy constraint atom and return new instance.
        """
        elements = []
        guard = [str(atom.guard[0]), ConstraintTerm.copy(atom.guard[1])]
        literal = int(atom.literal)
        term = ConstraintTerm.copy(atom.term)
        for element in atom.elements:
            elements.append(ConstraintElement.copy(element))
        return ConstraintAtom(elements, guard, literal, term)

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
        return ", ".join([str(term) for term in self.terms]) + condition

    def __repr__(self):
        return str(self)

    @staticmethod
    def copy(element):
        """
        Copy constraint element and return new instance.
        """
        terms = []
        for term in element.terms:
            terms.append(ConstraintTerm.copy(term))

        condition_id = None
        if isinstance(element.condition_id, int):
            condition_id = int(element.condition_id)

        return ConstraintElement(terms, None, condition_id)

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

    @staticmethod
    def copy(term):
        """
        Copy constraint term and return new instance.
        """
        if term.type == clingo.TheoryTermType.Number:
            return ConstraintTerm(None, int(term.number), [], clingo.TheoryTermType.Number)
        name = str(term.name)
        arguments = []
        for argument in term.arguments:
            arguments.append(ConstraintTerm.copy(argument))
        if len(arguments) == 0:
            term_type = clingo.TheoryTermType.Symbol
        else:
            term_type = clingo.TheoryTermType.Function
        return ConstraintTerm(name, None, arguments, term_type)

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
    def __init__(self, prg, appconfig, propconfig):
        self._prg = prg
        self._appconfig = appconfig
        self._propconfig = propconfig
        self._defined = {}
        self._auxvars = 0
        self._sum_constraints = set()
        self._aux_constraints = set()

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
        with self._prg.backend() as backend:
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
        with self._prg.backend() as backend:
            backend.add_rule(head, body, choice)
        if self._appconfig.print_trans:
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
            seperator = ":-" if body_str != "" else ""
            print(head_str, seperator, body_str, ".")

    def _add_defined(self, var, reason=None):
        if var not in self._defined:
            self._defined[var] = self._add_atom(clingo.Function("def", [self.term_to_symbol(var)]))
        defined_lit = self._defined[var]
        if reason is not None:
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
        if self._appconfig.print_trans:
            print()
            print("% Translating conditionals:", atom)
            print()
        elements = []
        neutral = ZERO
        if match(atom.term, "sum", 1):
            neutral = ZERO
        elif match(atom.term, "min", 1):
            neutral = ConstraintTerm(None, self._propconfig.max_int, None, clingo.TheoryTermType.Number)
        elif match(atom.term, "max", 1):
            neutral = ConstraintTerm(None, self._propconfig.min_int, None, clingo.TheoryTermType.Number)
        for element in atom.elements:
            if element.condition_id:
                cond = element.condition_id
                aux_var = self._add_auxvar()
                terms = [aux_var]
                terms.extend(element.terms[1:])
                elements.append(ConstraintElement(terms, None, None))
                self._add_defined(aux_var)
                holds_def = [self._add_defined(var) for var in self.vars(element.terms[0])]
                aux_var_elem = ConstraintElement([aux_var], None, None)
                holds_term = element.terms[0]
                holds = self._add_sum_constraint(ConstraintAtom([aux_var_elem], ["=", holds_term], None, SUM_TERM_HEAD))
                nholds = self._add_sum_constraint(ConstraintAtom([aux_var_elem], ["=", neutral], None, SUM_TERM_HEAD))
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
        type_term = ConstraintTerm(atom.term.name, None, [atom.term.arguments[0]], clingo.TheoryTermType.Function)
        self._translate_constraint(ConstraintAtom(elements, atom.guard, cond_free_lit, type_term))
        self._add_rule([cond_free_lit], [atom.literal])
        self._add_rule([atom.literal], [cond_free_lit])

    def _translate_assignment(self, atom):
        assert len(self.vars(atom.guard[1])) == 1 and not self.conditional(atom)
        if self._appconfig.print_trans:
            print()
            print("% Translating assignment:", atom)
            print()
        body = [atom.literal]
        for element in atom.elements:
            for var in self.vars(element.terms[0]):
                body.append(self._add_defined(var))
        type_term = ConstraintTerm(atom.term.name, None, [atom.term.arguments[0]], clingo.TheoryTermType.Function)
        head_lit = self._add_atom()
        self._translate_constraint(ConstraintAtom(atom.elements, ["=", atom.guard[1]], head_lit, type_term))
        self._add_rule([head_lit], body)

    def _translate_max(self, atom):
        assert not self.conditional(atom)
        if self._appconfig.print_trans:
            print()
            print("% Translating max aggregate:", atom)
            print()
        elements = []
        for element in atom.elements:
            terms = [ConstraintTerm("-", None, [element.terms[0]], clingo.TheoryTermType.Function)]
            for term in element.terms[1:]:
                terms.append(term)
            elements.append(ConstraintElement(terms, element.condition, element.condition_id))
        rel = atom.guard[0]
        if "<" in rel:
            rel = rel.replace("<", ">")
        elif ">" in rel:
            rel = rel.replace(">", "<")
        type_term = ConstraintTerm("min", None, [atom.term.arguments[0]], clingo.TheoryTermType.Function)
        rhs = ConstraintTerm("-", None, [atom.guard[1]], clingo.TheoryTermType.Function)
        head_lit = self._add_atom()
        self._translate_constraint(ConstraintAtom(elements, [rel, rhs], head_lit, type_term))
        self._add_rule([head_lit], [atom.literal])
        self._add_rule([atom.literal], [head_lit])

    def _translate_min(self, atom):
        assert not self.conditional(atom)
        if self._appconfig.print_trans:
            print()
            print("% Translating min aggregate:", atom)
            print()
        min_var = self._add_auxvar()
        min_def = self._add_defined(min_var)
        def_fact = False
        beta_lit = self._add_atom()
        for element in atom.elements:
            if not def_fact:
                body = []
                for var in self.vars(element.terms[0]):
                    body.append(self._add_defined(var))
                if len(body) == 0:
                    def_fact = True
                self._add_defined(min_var, body)

            check_lit = self._add_sum_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], ["<=", element.terms[0]], None, SUM_TERM_HEAD))
            self._add_rule([check_lit], [min_def])

            check_lit = self._add_sum_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], ["=", element.terms[0]], None, SUM_TERM_BODY))
            self._add_rule([check_lit], [min_def], True)
            self._add_rule([beta_lit], [check_lit])
        self._add_rule([], [-beta_lit, min_def])

        type_term = ConstraintTerm("sum", None, [atom.term.arguments[0]], clingo.TheoryTermType.Function)
        eq_lit = self._add_sum_constraint(ConstraintAtom([ConstraintElement([min_var], None, None)], atom.guard, None, type_term))
        self._add_rule([eq_lit], [atom.literal])
        self._add_rule([atom.literal], [eq_lit])

    def _translate_in(self, atom):
        assert not self.conditional(atom) and len(atom.elements) == 1 and atom.guard[0] == "="
        if self._appconfig.print_trans:
            print()
            print("% Translating range assignment:", atom)
            print()
        alpha_term = atom.elements[0].terms[0].arguments[0]
        beta_term = atom.elements[0].terms[0].arguments[1]
        alpha_lit = self._add_sum_constraint(ConstraintAtom([ConstraintElement([alpha_term], None, None)], ["<=", atom.guard[1]], None, SUM_TERM_HEAD))
        beta_lit = self._add_sum_constraint(ConstraintAtom([ConstraintElement([beta_term], None, None)], [">=", atom.guard[1]], None, SUM_TERM_HEAD))
        self._add_rule([alpha_lit], [atom.literal])
        self._add_rule([beta_lit], [atom.literal])

    def _add_sum_constraint(self, atom):
        if not isinstance(atom, ConstraintAtom):
            sum_con = ConstraintAtom.copy(atom)
        else:
            sum_con = atom
        for con in self._sum_constraints:
            if str(con) == str(sum_con):
                return con.literal
        if sum_con.literal is None:
            new_lit = self._add_atom()
            sum_con.literal = new_lit
        if self._appconfig.print_trans:
            print()
            print("% Adding sum constraint:", atom)
            print()
        self._sum_constraints.add(sum_con)
        defined = []
        for element in sum_con.elements:
            for var in self.vars(element.terms[0]):
                def_lit = self._add_defined(var)
                defined.append(def_lit)
                self._add_rule([], [sum_con.literal, -def_lit])
        for var in self.vars(sum_con.guard[1]):
            def_lit = self._add_defined(var)
            self._add_rule([], [sum_con.literal, -def_lit])
            defined.append(def_lit)
        if match(sum_con.term.arguments[0], "head", 0):
            self._define_variables(sum_con)
        elif match(sum_con.term.arguments[0], "body", 0):
            new_lit = self._add_atom()
            self._add_rule([new_lit], [], True)
            defined.append(new_lit)
            self._add_rule([sum_con.literal], defined)
            sum_con.literal = new_lit
        return sum_con.literal

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
        else:
            self._aux_constraints.add(ConstraintAtom.copy(atom))

    def _translate_constraints(self):
        for atom in self._prg.theory_atoms:
            self._translate_constraint(atom)

    def translate(self):
        """
        Translates ASP program with constraint atoms including assignments and conditionals into a Clingcon program.
        Adds rules implementing definition of variables, assignments, conditional linear constraint atoms and aggregates max and min.
        Returns sum constraints to be added to Clingcon.
        """
        self._translate_constraints()
        self._fix_undefined()
        self._prg.cleanup()
        return self._sum_constraints.union(self._aux_constraints)
