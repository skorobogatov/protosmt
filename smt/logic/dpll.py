from typing import Optional, Tuple, List, Set, Counter as CounterType
from enum import Enum, auto
from collections import Counter
from heapq import heappush, heappop

from smt.util import Unique, Memory, Transactional, TransactionalSet, TransactionalVector
from smt.logic import Sort, Expr, VariableSymbol, BooleanConnectiveSymbol, boolean, to_cnf


# -----------------------------------------------------------------------------


@Unique.cached
class Watch(Unique):
    clause: 'Clause'
    neighbour: 'Watch'
    literal: 'Transactional[Literal]'

    def __init__(self, mem: 'Memory', clause: 'Clause', master: 'bool') -> 'None':
        self.clause = clause
        self.neighbour = Watch(mem, clause, not master) if len(clause.literals) > 1 else self

    def update(self, assignment: 'Assignment') -> 'bool':
        assert assignment[self.literal.value] is False
        for λ in self.clause.literals:
            if (λ != self.neighbour.literal.value) and (assignment[λ] is not False):
                self.literal.value = λ
                return True
        return False


# -----------------------------------------------------------------------------


@Unique.cached
@Unique.transform_args(lambda mem, *literals: (mem, *sorted(literals)))
class Clause(Unique):
    literals: 'Tuple[Literal, ...]'
    __a: 'Watch'
    __b: 'Watch'

    def __init__(self, mem: 'Memory', *literals: 'Literal') -> 'None':
        self.literals = tuple(sorted(literals))
        self.__a = Watch(mem, self, True)
        self.__b = self.__a.neighbour
        self.__a.literal = Transactional(mem, literals[0])
        literals[0].watches.append(self.__a)
        if self.__a != self.__b:
            self.__b.literal = Transactional(mem, literals[1])
            literals[1].watches.append(self.__b)

    def is_conflict(self, assignment: 'Assignment') -> 'bool':
        p, q = self.__a.literal.value, self.__b.literal.value
        return (assignment[p] is False) and (assignment[q] is False)

    def derive(self, assignment: 'Assignment') -> 'Optional[Literal]':
        p, q = self.__a.literal.value, self.__b.literal.value
        if ((assignment[p] is False) or (p == q)) and (assignment[q] is None):
            return q
        if (assignment[q] is False) and (assignment[p] is None):
            return p
        return None


# -----------------------------------------------------------------------------


@Unique.cached
class LiteralPos(Unique):
    index: 'Transactional[int]'
    link: 'Transactional[Literal]'
    antecedent: 'Transactional[Optional[Clause]]'

    def __init__(self, mem: 'Memory', expr: 'Expr') -> 'None':
        self.index = Transactional(mem, 0)
        self.link = Transactional(mem, Literal(mem, expr))
        self.antecedent = Transactional(mem, None)


@Unique.cached
class Literal(Unique):
    expr: 'Expr'
    negated: 'Literal'
    watches: 'TransactionalVector[Watch]'
    __pos: 'LiteralPos'

    def __init__(self, mem: 'Memory', expr: 'Expr') -> 'None':
        assert expr.symbol.sort == Sort.BOOL
        self.expr, self.negated = expr, Literal(mem, expr.negated)
        self.watches = TransactionalVector(mem)
        self.__pos = LiteralPos(mem, expr if expr < expr.negated else expr.negated)

    @property
    def index(self) -> 'int':
        return self.__pos.index.value

    @index.setter
    def index(self, value: 'int') -> 'None':
        self.__pos.index.value = value

    @property
    def link(self) -> 'Literal':
        return self.__pos.link.value

    @link.setter
    def link(self, value: 'Literal') -> 'None':
        self.__pos.link.value = value

    @property
    def antecedent(self) -> 'Optional[Clause]':
        return self.__pos.antecedent.value

    @antecedent.setter
    def antecedent(self, value: 'Optional[Clause]') -> 'None':
        self.__pos.antecedent.value = value


# -----------------------------------------------------------------------------


class Assignment:
    __mem: 'Memory'
    sentinel: 'Literal'
    top_decision: 'Transactional[Literal]'
    literals: 'TransactionalVector[Literal]'
    border: 'Transactional[int]'
    __i: 'Transactional[int]'
    __j: 'Transactional[int]'

    def __init__(self, mem: 'Memory', *literals: 'Literal') -> 'None':
        self.__mem = mem
        self.sentinel = Literal(mem, boolean(False))  # TODO: what if formula contains False?
        self.top_decision = Transactional(mem, self.sentinel)

        self.literals = TransactionalVector(mem)
        self.literals.append(self.sentinel)
        for λ in literals:
            λ.index = len(self.literals)
            self.literals.append(λ)
        self.border = Transactional(mem, 1)
        self.__i = Transactional(mem, 1)
        self.__j = Transactional(mem, 0)

    def __getitem__(self, lit: 'Literal') -> 'Optional[bool]':
        index = lit.index
        assert (0 < index < len(self.literals)) and \
               (self.literals[index] == lit or self.literals[index] == lit.negated)
        return self.literals[index] == lit.negated if index < self.border.value else None

    def make_decision(self, lit: 'Literal') -> 'None':
        self.__place_literal(lit)
        lit.link = lit
        lit.antecedent = None
        self.top_decision.value.link = lit
        self.top_decision.value = lit

    def make_implication(self, lit: 'Literal', antecedent: 'Clause') -> 'None':
        self.__place_literal(lit)
        lit.link = self.top_decision.value
        lit.antecedent = antecedent

    def __place_literal(self, lit: 'Literal') -> 'None':
        assert self[lit] is None
        if lit.index != self.border.value:
            self.literals[lit.index] = border_lit = self.literals[self.border.value]
            border_lit.index = lit.index
            lit.index = self.border.value
        self.literals[self.border.value] = lit
        self.border.value += 1

    def get_suspicious_clause(self) -> 'Optional[Clause]':
        while True:
            if self.__i.value == self.border.value:
                return None
            lit = self.literals[self.__i.value]
            if self.__j.value == len(lit.watches):
                self.__i.value += 1
                self.__j.value = 0
            else:
                w = lit.watches[self.__j.value]
                w_lit = w.literal.value
                if not w.update(self):
                    self.__j.value += 1
                    return w.clause
                w_lit.watches.remove_by_pop(self.__j.value)
                w.literal.value.watches.append(w)

    def analyze_conflict(self, clause: 'Clause') -> 'List[Literal]':
        assert clause.is_conflict(self)

        top = self.top_decision.value
        heap: 'List[int]' = []
        visited: 'Set[Literal]' = set()

        def push_literals(c: 'Clause') -> 'int':
            n = 0
            for λ in c.literals:
                if (λ not in visited) and (λ.negated not in visited):
                    heappush(heap, -λ.index)
                    if λ.link == top or λ == top:
                        n += 1
                    visited.add(λ)
            return n

        count = push_literals(clause)
        res: 'List[Literal]' = []
        while len(heap) > 0:
            lit = self.literals[-heappop(heap)]
            if (lit.link != top) or (count == 1):
                res.append(lit)
            else:
                assert lit.antecedent is not None
                count += push_literals(lit.antecedent) - 1
        return res

    def backtrack(self, lit: 'Literal') -> 'None':
        assert (self[lit] is False) and (lit.antecedent is None)
        self.border.value = lit.index
        if self.__i.value >= lit.index:
            self.__i.value, self.__j.value = lit.index, 0

        last = self.literals[lit.index - 1]
        top = last.link
        if top == lit:
            top = last
        top.link = top
        self.top_decision.value = top


# -----------------------------------------------------------------------------


class Status(Enum):
    SAT = auto()
    UNSAT = auto()

    def __str__(self) -> 'str':
        return "SAT" if self is Status.SAT else "UNSAT"


class Model:
    __mem: 'Memory'
    __clauses: 'Set[Clause]'
    __literals: 'CounterType[Literal]'
    assignment: 'Assignment'
    __learnt_clauses: 'TransactionalSet[Clause]'
    status: 'Optional[Status]'

    def __init__(self, expr: 'Expr') -> 'None':
        self.__mem = Memory()
        self.__clauses, self.__literals = set(), Counter()

        cnf_expr = to_cnf(expr)
        if cnf_expr.symbol == BooleanConnectiveSymbol(True):
            for ε in cnf_expr.args:
                self.__make_clause(ε)
        else:
            self.__make_clause(cnf_expr)

        literals = sorted(self.__literals.items(), key=lambda p: -p[1])
        self.assignment = Assignment(self.__mem, *(λ for λ, _ in literals))

        self.__learnt_clauses = TransactionalSet(self.__mem)
        self.status = None

    def __make_clause(self, expr: 'Expr') -> 'None':
        assert expr.symbol != BooleanConnectiveSymbol(True)
        es = expr.args if expr.symbol == BooleanConnectiveSymbol(False) else (expr,)
        clause = Clause(self.__mem, *(self.__make_literal(ε) for ε in es))
        self.__clauses.add(clause)

    def __make_literal(self, expr: 'Expr') -> 'Literal':
        assert not isinstance(expr.symbol, BooleanConnectiveSymbol)
        lit = Literal(self.__mem, expr)
        self.__literals[lit if lit < lit.negated else lit.negated] += 1
        return lit

    def solve(self) -> 'None':
        while True:
            while True:
                clause = self.assignment.get_suspicious_clause()
                if clause is None:
                    break
                if clause.is_conflict(self.assignment):
                    literals = self.assignment.analyze_conflict(clause)
                    x = literals[0]
                    if len(literals) == 1:
                        if x.link == self.assignment.sentinel:
                            self.status = Status.UNSAT
                            return
                        backtrack_lit = self.assignment.sentinel.link
                        if backtrack_lit != self.assignment.sentinel:
                            self.assignment.backtrack(backtrack_lit)
                    else:
                        y = literals[1]
                        backtrack_lit = y.link if y.antecedent is None else y.link.link
                        assert backtrack_lit != self.assignment.sentinel
                        self.assignment.backtrack(backtrack_lit)
                    asserting_clause = Clause(self.__mem, *literals)
                    self.__learnt_clauses.add(asserting_clause)
                    self.assignment.make_implication(x.negated, asserting_clause)
                else:
                    z = clause.derive(self.assignment)
                    if z is not None:
                        self.assignment.make_implication(z.negated, clause)
            border = self.assignment.border.value
            if border == len(self.assignment.literals):
                self.status = Status.SAT
                return
            self.assignment.make_decision(self.assignment.literals[border])

    def eval(self, expr: 'Expr') -> 'Optional[Expr]':
        assert (expr.symbol.sort is Sort.BOOL) and isinstance(expr.symbol, VariableSymbol)
        lit = Literal(self.__mem, expr)
        if (lit not in self.__literals) and (lit.negated not in self.__literals):
            return None
        value = self.assignment[lit]
        return None if value is None else boolean(value)

# -----------------------------------------------------------------------------
