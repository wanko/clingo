import sys
import clingo

try:
    # Note: Can be installed to play with realistic domain sizes.
    from sortedcontainers import SortedDict
    _HAS_SC = True
except ImportError:
    _HAS_SC = False

MAX_INT = 20
MIN_INT = -20
TRUE_LIT = 1

def lerp(x, y):
    # NOTE: integer division with floor
    return x + (y - x) // 2

def match(term, name, arity):
    return (term.type in (clingo.TheoryTermType.Function, clingo.TheoryTermType.Symbol) and
            term.name == name and
            len(term.arguments) == arity)

def remove_if(rng, pred):
    j = 0
    for i, x in enumerate(rng):
        if pred(x):
            continue
        if i != j:
            rng[i], rng[j] = rng[j], rng[i]
        j += 1
    return j

class Constraint(object):
    def __init__(self, atom, literal, is_sum):
        self.literal = literal
        self.rhs = self._parse_num(atom.guard[1])
        self.vars = []

        # combine coefficients
        seen = {}
        for i, (co, var) in enumerate(self._parse_elems(atom.elements, is_sum)):
            if co == 0:
                continue
            if var not in seen:
                seen[var] = i
                self.vars.append((co, var))
            else:
                self.vars[seen[var]][0] += co

        # drop zero weights
        self.vars = [(co, var) for co, var in self.vars if co != 0]

    def _parse_elems(self, elems, is_sum):
        for elem in elems:
            if len(elem.terms) == 1 and not elem.condition:
                # python 3 has yield from
                for x in self._parse_elem(elem.terms[0], is_sum):
                    yield x
            else:
                raise RuntimeError("Invalid Syntax")

    def _parse_elem(self, term, is_sum):
        if not is_sum:
            if match(term, "-", 2):
                yield 1, self._parse_var(term.arguments[0])
                yield -1, self._parse_var(term.arguments[1])
            else:
                raise RuntimeError("Invalid Syntax")
        else:
            if match(term, "+", 2):
                for x in self._parse_elem(term.arguments[0], True):
                    yield x
                for x in self._parse_elem(term.arguments[1], True):
                    yield x
            elif match(term, "*", 2):
                num = self._parse_num(term.arguments[0])
                var = self._parse_var(term.arguments[1])
                yield num, var
            else:
                raise RuntimeError("Invalid Syntax")

    def _parse_num(self, term):
        if term.type == clingo.TheoryTermType.Number:
            return term.number
        elif (term.type == clingo.TheoryTermType.Symbol and
                term.symbol.type == clingo.SymbolType.Number):
            return term.symbol.number
        elif match(term, "-", 1):
            return -self._parse_num(term.arguments[0])
        elif match(term, "+", 1):
            return +self._parse_num(term.arguments[0])
        else:
            raise RuntimeError("Invalid Syntax")

    def _parse_var(self, term):
        return str(term)

    def __str__(self):
        return "{} <= {}".format(self.vars, self.rhs)


class VarState(object):
    def __init__(self, var):
        self.var = var
        self._upper_bound = [MAX_INT]
        self._lower_bound = [MIN_INT]
        # TODO: needs better container
        if _HAS_SC:
            self.literals = SortedDict()
        else:
            self.literals = (MAX_INT-MIN_INT)*[None]

    def push_lower(self):
        self._lower_bound.append(self.lower_bound)

    def push_upper(self):
        self._upper_bound.append(self.upper_bound)

    def pop_lower(self):
        assert len(self._lower_bound) > 1
        self._lower_bound.pop()

    def pop_upper(self):
        assert len(self._upper_bound) > 1
        self._upper_bound.pop()

    @property
    def lower_bound(self):
        assert self._lower_bound
        return self._lower_bound[-1]

    @lower_bound.setter
    def lower_bound(self, value):
        assert self._lower_bound
        self._lower_bound[-1] = value

    @property
    def upper_bound(self):
        assert self._upper_bound
        return self._upper_bound[-1]

    @upper_bound.setter
    def upper_bound(self, value):
        assert self._upper_bound
        self._upper_bound[-1] = value

    @property
    def is_assigned(self):
        return self.upper_bound == self.lower_bound

    def has_literal(self, value):
        if value < MIN_INT or value >= MAX_INT:
            return True
        if _HAS_SC:
            return value in self.literals
        return self.literals[value - MIN_INT] is not None

    def get_literal(self, value):
        assert MIN_INT <= value < MAX_INT and self.has_literal(value)
        if _HAS_SC:
            return self.literals[value]
        return self.literals[value - MIN_INT]

    def prev_literal(self, value):
        assert MIN_INT <= value < MAX_INT and self.has_literal(value)
        if _HAS_SC:
            prev, _ = self.literals.peekitem(self.literals.bisect_left(value))
            return prev if value < prev else None
        for prev in range(value-1, MIN_INT-1, -1):
            if self.has_literal(prev):
                return prev
        return None

    def succ_literal(self, value):
        assert MIN_INT <= value < MAX_INT and self.has_literal(value)
        if _HAS_SC:
            i = self.literals.bisect_right(value)
            if i == len(self.literals):
                return None
            succ, _ = self.literals.peekitem()
            return succ
        for succ in range(value+1, MAX_INT):
            if self.has_literal(succ):
                return succ
        return None

    def set_literal(self, value, lit):
        assert MIN_INT <= value < MAX_INT
        if _HAS_SC:
            self.literals[value] = lit
        else:
            self.literals[value - MIN_INT] = lit

    def unset_literal(self, value):
        assert MIN_INT <= value < MAX_INT
        if _HAS_SC:
            del self.literals[value]
        else:
            self.literals[value - MIN_INT] = None

    def __repr__(self):
        return "{}=[{},{}]".format(self.var, self.lower_bound, self.upper_bound)

class TodoList(object):
    def __init__(self):
        self._seen = set()
        self._list = []

    def __len__(self):
        return len(self._list)

    def __contains__(self, x):
        return x in self._seen

    def __iter__(self):
        return iter(self._list)

    def __getitem__(self, val):
        return self._list[val]

    def add(self, x):
        if x not in self:
            self._seen.add(x)
            self._list.append(x)
            return True
        return False

    def extend(self, i):
        for x in i:
            self.add(x)

    def clear(self):
        self._seen.clear()
        self._list.clear()

class Level(object):
    def __init__(self, level):
        self.level = level
        # a trail-like data structure would also be possible but then
        # assignments would have to be undone
        self.undo_upper = TodoList()
        self.done_upper = 0
        self.undo_lower = TodoList()
        self.done_lower = 0

class State(object):
    def __init__(self, l2c, vl2c, vu2c):
        self._vars = []
        self._var_state = {}
        self._litmap = {}
        self._levels = [Level(0)]
        self._vl2c = vl2c
        self._vu2c = vu2c
        self._l2c = l2c
        self._todo = TodoList()
        self._facts_integrated = [(0, 0)]

    def get_assignment(self, variables):
        vvs = zip(variables, self._vars)
        return [(v, vs.lower_bound) for v, vs in vvs]

    def get_value(self, var):
        return (self._var_state[var].lower_bound
                if var in self._var_state else
                MIN_INT)

    def _push_level(self, level):
        if self._levels[-1].level < level:
            self._levels.append(Level(level))

    def _pop_level(self):
        self._levels.pop()

    def _state(self, var):
        return self._var_state[var]

    @property
    def _level(self):
        return self._levels[-1]

    def _get_literal(self, vs, value, control):
        if value < MIN_INT:
            return -TRUE_LIT
        if value >= MAX_INT:
            return TRUE_LIT
        if not vs.has_literal(value):
            lit = control.add_literal()
            vs.set_literal(value, lit)
            self._litmap.setdefault(lit, []).append((vs, value))
            control.add_watch(lit)
            control.add_watch(-lit)
        return vs.get_literal(value)

    def _update_literal(self, vs, value, control, truth):
        if value < MIN_INT or value >= MAX_INT or truth is None:
            return None, self._get_literal(vs, value, control)
        lit = TRUE_LIT if truth else -TRUE_LIT
        if not vs.has_literal(value):
            vs.set_literal(value, lit)
            self._litmap.setdefault(lit, []).append((vs, value))
            return None, lit
        old = vs.get_literal(value)
        if old == lit:
            return None, lit
        vs.set_literal(value, lit)
        vec = self._litmap[old]
        assert (vs, value) in vec
        vec.remove((vs, value))
        if not vec:
            assert -old not in self._litmap
            del self._litmap[old]
            control.remove_watch(old)
            control.remove_watch(-old)
        self._litmap.setdefault(lit, []).append((vs, value))
        return old, lit

    # initialization
    def init_domain(self, variables):
        for v in variables:
            vs = VarState(v)
            self._var_state[v] = vs
            self._vars.append(vs)

    # propagation
    def propagate(self, control, changes):
        ass = control.assignment

        # open a new decision level if necessary
        self._push_level(ass.decision_level)

        # propagate order literals that became true/false
        for lit in changes:
            self._todo.extend(self._l2c.get(lit, []))
            if not self._update_domain(control, lit):
                return False

        return True

    def _propagate_variable(self, control, vs, value, lit, sign):
        assert vs.has_literal(value)
        ass = control.assignment
        assert ass.is_true(lit)

        # get the literal to propagate
        l = sign * self._get_literal(vs, value, control)

        # on-the-fly simplify
        if ass.level(lit) == 0 and ass.level(l) > 0:
            o, l = self._update_literal(vs, value, control, sign > 0)
            o, l = sign * o, sign * l
            if not control.add_clause([o], lock=True):
                return False

        # propagate the literal
        if not ass.is_true(l) and not control.add_clause([-lit, l]):
            return False

        return True

    def _update_domain(self, control, lit):
        """
        The function updates lower and upper bounds of variables and propagates
        order literals.

        If a variable `v` has lower bound `l`, then the preceeding order (if
        any) literal `v<=l'` with `l'<l` is made false. Similarly, if a
        variable `v` has upper bound `u`, then the succeeding order literal
        `v<=u'` with `u'<u` is made true.

        Problems
        ========
        - Clauses could be locked.
        """
        assert control.assignment.is_true(lit)

        lvl = self._level

        # update and propagate upper bound
        if lit in self._litmap:
            start = self._facts_integrated[-1][0] if lit == TRUE_LIT else None
            for vs, value in self._litmap[lit][start:]:
                # update upper bound
                if vs.upper_bound > value:
                    if lvl.undo_upper.add(vs):
                        vs.push_upper()
                    vs.upper_bound = value
                    self._todo.extend(self._vu2c.get(vs.var, []))

                # make succeeding literal true
                succ = vs.succ_literal(value)
                if succ is not None and not self._propagate_variable(control, vs, succ, lit, 1):
                    return False

        # update and propagate lower bound
        if -lit in self._litmap:
            start = self._facts_integrated[-1][1] if lit == TRUE_LIT else None
            for vs, value in self._litmap[-lit][start:]:
                # update lower bound
                if vs.lower_bound < value+1:
                    if lvl.undo_lower.add(vs):
                        vs.push_lower()
                    vs.lower_bound = value+1
                    self._todo.extend(self._vl2c.get(vs.var, []))

                # make preceeding literal false
                prev = vs.prev_literal(value)
                if prev is not None and not self._propagate_variable(control, vs, prev, lit, -1):
                    return False

        return True

    def propagate_constraint(self, l, c, control):
        """
        This function propagates a constraint that became active because an its
        associated literal became true.

        The function calculates the slack of the constraint w.r.t. to the
        lower/upper bounds of its values. The order values are then propagated
        in such a way that the slack is positive. The trick here is that we can
        use the ordering of variables to restrict the number of propagations.
        For example, for positive coefficients, we just have to enforce the
        smallest order variable that would make the slack non-negative.
        """
        ass = control.assignment
        assert not ass.is_false(l)

        # NOTE: recalculation could be avoided by maintaing per clause state
        #       (but the necessary data structure would be quite complicated)
        slack = c.rhs  # sum of lower bounds (also saw this called slack)
        lbs = []       # lower bound literals
        num_guess = 0  # number of assignments above level 0
        for i, (co, var) in enumerate(c.vars):
            vs = self._state(var)
            if co > 0:
                slack -= co*vs.lower_bound
                # note that any literal associated with a value smaller than
                # the lower bound is false
                lit = self._get_literal(vs, vs.lower_bound-1, control)
            else:
                slack -= co*vs.upper_bound
                # note that any literal associated with a value greater or
                # equal than the upper bound is true
                lit = -self._get_literal(vs, vs.upper_bound, control)

            assert ass.is_false(lit)
            if ass.level(lit) > 0:
                num_guess += 1
            lbs.append(lit)
        if ass.level(l) > 0:
            num_guess += 1

        lbs.append(-l)

        # this is necessary to correctly handle empty constraints (and do
        # propagation of false constraints)
        if slack < 0:
            yield lbs

        if not ass.is_true(l):
            return True

        for i, (co, var) in enumerate(c.vars):
            vs = self._state(var)

            # adjust the number of guesses if the current literal is a guess
            adjust = 1 if ass.level(lbs[i]) > 0 else 0

            # if all literals are assigned on level 0 then we can associate the
            # value with a true/false literal, taken care of by the extra
            # argument truth to _update_literal
            if co > 0:
                truth = num_guess == adjust or None
                diff = slack+co*vs.lower_bound
                value = diff//co
                old, lit = self._update_literal(vs, value, control, truth)
                if old is not None and not control.add_clause([old], lock=True):
                    return False
            else:
                truth = num_guess > adjust and None
                diff = slack+co*vs.upper_bound
                value = -(diff//-co)
                old, lit = self._update_literal(vs, value-1, control, truth)
                lit = -lit
                if old is not None and not control.add_clause([-old], lock=True):
                    return False

            # the value is chosen in a way that the slack is greater or equal
            # than 0 but also so that it does not exceed the coefficient (in
            # which case the propagation would not be strong enough)
            assert diff - co*value >= 0 and diff - co*value < abs(co)

            if not ass.is_true(lit):
                lbs[i], lit = lit, lbs[i]
                yield lbs
                lbs[i] = lit

    def undo(self):
        lvl = self._level
        for vs in lvl.undo_lower:
            vs.pop_lower()
        lvl.undo_lower.clear()
        for vs in lvl.undo_upper:
            vs.pop_upper()
        self._pop_level()

    # checking
    @property
    def _num_facts(self):
        return len(self._litmap.get(1, [])), len(self._litmap.get(-1, []))

    def check(self, control):
        ass = control.assignment

        # Note: Maintain which facts have been integrated on which level.
        assert ass.decision_level <= len(self._facts_integrated)
        if ass.decision_level == len(self._facts_integrated):
            self._facts_integrated.append(self._facts_integrated[-1])
        del self._facts_integrated[ass.decision_level+1:]

        # Note: We have to loop here because watches for the true/false
        # literals do not fire again.
        while True:
            # Note: This integrates any facts that have not been integrated yet
            # on the current decision level.
            if not self._update_domain(control, 1):
                return False
            num_facts = self._num_facts
            self._facts_integrated[-1] = num_facts

            # propagate affected constraints
            for c in self._todo:
                lit = c.literal
                if not ass.is_false(lit):
                    for clause in self.propagate_constraint(lit, c, control):
                        if not control.add_clause(clause) or not control.propagate():
                            self._todo.clear()
                            return False
            self._todo.clear()

            if num_facts == self._num_facts:
                break

        return True

    def check_full(self, control):
        for vs in self._vars:
            if not vs.is_assigned:
                value = lerp(vs.lower_bound, vs.upper_bound)
                self._get_literal(vs, value, control)
                return

    # reinitialization
    def _remove_literals(self, lit, pred):
        if lit in self._litmap:
            variables = self._litmap[lit]
            i = remove_if(variables, pred)
            assert i > 0
            for vs, value in variables[i:]:
                vs.unset_literal(value)
            del variables[i:]

    def remove_literals(self):
        # remove solve step local variables
        # Note: Iteration order does not matter.
        remove = [(lit, vss)
                  for lit, vss in self._litmap.items()
                  if abs(lit) != TRUE_LIT]
        for lit, vss in remove:
            for vs, value in vss:
                vs.unset_literal(value)
            del self._litmap[lit]

        # remove literals above upper or below lower bound
        self._remove_literals(TRUE_LIT, lambda x: x[1] != x[0].upper_bound)
        self._remove_literals(-TRUE_LIT, lambda x: x[1] != x[0].lower_bound-1)

    def update_bounds(self, init, other):
        assert len(other._litmap) <= 2

        # update upper bounds
        for vs_b, _ in other._litmap.get(TRUE_LIT, []):
            vs_a = self._var_state[vs_b.var]
            if vs_b.upper_bound < vs_a.upper_bound:
                old, _ = self._update_literal(vs_a, vs_b.upper_bound, init, True)
                if old is not None and not init.add_clause([old]):
                    return False

        # update lower bounds
        for vs_b, _ in other._litmap.get(-TRUE_LIT, []):
            vs_a = self._var_state[vs_b.var]
            if vs_a.lower_bound < vs_b.lower_bound:
                old, _ = self._update_literal(vs_a, vs_b.lower_bound-1, init, False)
                if old is not None and not init.add_clause([-old]):
                    return False
        return self._update_domain(init, 1)


class Propagator(object):
    def __init__(self):
        self._l2c = {}     # map literals to constraints
        self._states = []  # map thread id to states
        self._vars = []    # list of variables
        self._vl2c = {}    # map variables affecting lower bound of constraints
        self._vu2c = {}    # map variables affecting upper bound of constraints

    def _state(self, thread_id):
        while len(self._states) <= thread_id:
            self._states.append(State(self._l2c, self._vl2c, self._vu2c))
        return self._states[thread_id]

    def init(self, init):
        init.check_mode = clingo.PropagatorCheckMode.Fixpoint

        constraints = []
        variables = []
        variables_seen = set(self._vars)
        for atom in init.theory_atoms:
            is_sum = match(atom.term, "sum", 0)
            is_diff = match(atom.term, "diff", 0)
            if is_sum or is_diff:
                c = Constraint(atom, init.solver_literal(atom.literal), is_sum)
                constraints.append(c)
                self._l2c.setdefault(c.literal, []).append(c)
                init.add_watch(c.literal)
                for co, var in c.vars:
                    if var not in variables_seen:
                        variables_seen.add(var)
                        variables.append(var)
                    if co > 0:
                        self._vl2c.setdefault(var, []).append(c)
                    else:
                        self._vu2c.setdefault(var, []).append(c)

        # replace all non-fact order literals by None in states
        for state in self._states:
            state.remove_literals()

        # gather bounds of states in master
        if self._states:
            master = self._states[0]
            for state in self._states[1:]:
                if not master.update_bounds(init, state):
                    return

        # adjust number of threads if necessary
        del self._states[init.number_of_threads:]
        if self._vars:
            for i in range(len(self._states), init.number_of_threads):
                state = self._state(i)
                state.init_domain(self._vars)

        # add newly introduced variables
        self._vars.extend(variables)
        for i in range(init.number_of_threads):
            state = self._state(i)
            state.init_domain(variables)

        # propagate bounds in master to other states
        master = self._states[0]
        for state in self._states[1:]:
            if not state.update_bounds(init, master):
                return

        ass = init.assignment
        intrail = set()
        trail = []
        # TODO: Could be a member (of the states) if we had access to clasp's
        # trail.
        trail_offset = 0

        # propagate the newly added constraints
        # Note: consequences of previously added constraints are stored in the
        # bounds propagated above.
        for state in self._states:
            state._todo.extend(constraints)

        # Note: The initial propagation below, will not introduce any order
        # literals other than true or false.
        while True:
            if not init.propagate():
                return

            # TODO: Trail handling should happen in clingo.
            for var in range(1, ass.max_size):
                if var in intrail:
                    continue
                t = ass.value(var)
                if t is True:
                    trail.append(var)
                    intrail.add(var)
                if t is False:
                    trail.append(-var)
                    intrail.add(var)

            # Note: Initially, the trail is guaranteed to have at least size 1.
            # This ensures that order literals will be propagated.
            if trail_offset == len(trail):
                break
            trail_offset = len(trail)

            for state in self._states:
                # Note: propagation won't add anything to the trail
                if not state.propagate(init, trail[trail_offset:]):
                    return

                if not state.check(init):
                    return

    def propagate(self, control, changes):
        state = self._state(control.thread_id)
        state.propagate(control, changes)

    def check(self, control):
        size = control.assignment.size
        state = self._state(control.thread_id)

        if not state.check(control):
            return

        # TODO: Should assignment.is_total be true even after new literals have
        # been added?
        # make sure that all variables are assigned in the end
        if size == control.assignment.size and control.assignment.is_total:
            state.check_full(control)

    def undo(self, thread_id, assign, changes):
        self._state(thread_id).undo()

    def get_assignment(self, thread_id):
        return self._state(thread_id).get_assignment(self._vars)

    def get_value(self, symbol, thread_id):
        return self._state(thread_id).get_value(str(symbol))


class Application(object):
    def __init__(self):
        self.program_name = "csp"
        self.version = "1.0"
        self._propagator = Propagator()
        self._bound_symbol = None
        self._bound_value = None

    def print_model(self, model, default_printer):
        ass = self._propagator.get_assignment(model.thread_id)

        default_printer()

        print("Valid assignment for constraints found:")
        print(" ".join("{}={}".format(n, v) for n, v in ass))

        if self._bound_symbol is not None:
            print("CSP Optimization: {}".format(self._get_bound(model)))

    def _parse_min(self, value):
        global MIN_INT
        MIN_INT = int(value)
        return True

    def _parse_max(self, value):
        global MAX_INT
        MAX_INT = int(value)
        return True

    def _parse_minimize(self, value):
        term = clingo.parse_term("({},)".format(value))
        args = term.arguments
        size = len(args)
        if size == 0 or size > 2 or (size > 1 and args[1].type != clingo.SymbolType.Number):
            return False
        self._bound_symbol = args[0]
        if size > 1:
            self._bound_value = args[1].number
        return True

    def register_options(self, options):
        group = "CSP Options"
        options.add(group, "min-int", "Minimum integer [-20]", self._parse_min, argument="<i>")
        options.add(group, "max-int", "Maximum integer [20]", self._parse_max, argument="<i>")
        options.add(group, "minimize-variable",
            "Minimize the given variable\n"
            "      <arg>   : <variable>[,<initial>]\n"
            "      <variable>: the variable to minimize_\n"
            "      <initial> : upper bound for the variable\n",
            self._parse_minimize)

    def validate_options(self):
        if MIN_INT > MAX_INT:
            raise RuntimeError("min-int must not be larger than max-int")

    def _get_bound(self, model):
        return self._propagator.get_value(self._bound_symbol, model.thread_id)

    def main(self, prg, files):
        for f in files:
            prg.load(f)
        prg.register_propagator(self._propagator)
        prg.add("base", [], """\
#theory cp {
    constant  { - : 1, unary };
    diff_term {
    - : 0, binary, left
    };
    sum_term {
    - : 2, unary;
    * : 1, binary, left;
    + : 0, binary, left
    };
    &sum/0 : sum_term, {<=}, constant, head;
    &diff/0 : diff_term, {<=}, constant, head
}.
""")

        prg.ground([("base", [])])
        if self._bound_symbol is None:
            prg.solve()
        else:
            # Note: This is to mirror the implementation in clingo-dl. In
            # principle this could be dealt with differently with order
            # variables.
            prg.add("__bound", ("s", "b"), "&sum { 1*s } <= b.")

            found = True
            while found:
                if self._bound_value is not None:
                    prg.ground((("__bound", (
                        self._bound_symbol,
                        clingo.Number(self._bound_value - 1))),))

                found = False
                for model in prg.solve(yield_=True):
                    self._bound_value = self._get_bound(model)
                    found = True
                    break


if __name__ == "__main__":
    sys.exit(int(clingo.clingo_main(Application(), sys.argv[1:])))
