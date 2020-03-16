import clingo
from csp.astutil import match

class Translator(object):
    '''
    Class that translates ASP program with constraint atoms including assignments and conditionals into a Clingcon program.
    '''
    def __init__(self, theory_atoms, backend):
        self._theory_atoms = theory_atoms
        self._backend = backend
        self._defined = {}

    def vars(self, term):
        '''
        Return all variables in a term.
        '''
        if term.type == clingo.SymbolType.Number:
            return set()
        elif match(term, "-", 2) or match(term, "+", 2) or match(term, "*", 2) or match(term, "..", 2):
            return self.vars(term.arguments[0]).union(self.vars(term.arguments[1]))
        elif match(term, "-", 1) or match(term, "+", 1):
            return self.vars(term.arguments[0])
        elif term.type in (clingo.TheoryTermType.Symbol, clingo.TheoryTermType.Function, clingo.TheoryTermType.Tuple):
            return {term}
        else:
            return set()

    def term_to_symbol(self, term):
        if not term.arguments:
            return clingo.Function(term.name)
        else:
            return clingo.Function(term.name, [self.term_to_symbol(arg) for arg in term.arguments])

    def _add_defined(self, var, reason):
        with self._backend as backend:
            self._defined[var] = backend.add_atom(clingo.Function("def", [self.term_to_symbol(var)]))
            backend.add_rule([self._defined[var]], reason)

    def _define_variables(self):
        for atom in self._theory_atoms:
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

    def _translate_constraints(self):
        pass

    def translate(self):
        self._define_variables()
        self._translate_constraints()
