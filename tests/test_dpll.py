from typing import List, Set
from unittest import TestCase

from smt.util import Memory
from smt.logic.symbols_base import ValencySymbol, NullaryValencyMixin, BooleanMixin
from smt.logic.dpll import Literal, Clause, Assignment, Status


# -----------------------------------------------------------------------------

class TestClauses(TestCase):
    class A(ValencySymbol, NullaryValencyMixin, BooleanMixin):
        pass

    def setUp(self) -> 'None':
        self.__mem = Memory()

    def new_lit(self) -> 'Literal':
        return Literal(self.__mem, TestClauses.A().apply())

    def new_clause(self, *literals: 'Literal') -> 'Clause':
        return Clause(self.__mem, *literals)

    def test_assignment(self):
        u = self.new_lit()
        v = self.new_lit()
        x = self.new_lit()
        y = self.new_lit()
        z = self.new_lit()
        a = Assignment(self.__mem, u, v, x, y, z)

        self.assertEqual(a.sentinel, a.sentinel.link)
        self.assertEqual(a.sentinel, a.top_decision.value)

        a.make_decision(u)
        a.make_decision(v)
        self.assertFalse(a[u])
        self.assertFalse(a[v])
        self.assertIsNone(a[x])
        self.assertIsNone(a[y])
        self.assertIsNone(a[z])

        a.make_decision(x)
        a.make_decision(y)
        self.assertFalse(a[u])
        self.assertFalse(a[v])
        self.assertFalse(a[x])
        self.assertFalse(a[y])
        self.assertIsNone(a[z])

        self.assertEqual(u, a.sentinel.link)
        self.assertEqual(v, u.link)
        self.assertEqual(x, v.link)
        self.assertEqual(y, x.link)
        self.assertEqual(y, y.link)
        self.assertEqual(y, a.top_decision.value)

        a.backtrack(x)
        self.assertFalse(a[u])
        self.assertFalse(a[v])
        self.assertIsNone(a[x])
        self.assertIsNone(a[y])
        self.assertIsNone(a[z])

        a.make_decision(y)
        a.make_decision(z)
        self.assertFalse(a[u])
        self.assertFalse(a[v])
        self.assertIsNone(a[x])
        self.assertFalse(a[y])
        self.assertFalse(a[z])

        self.assertEqual(u, a.sentinel.link)
        self.assertEqual(v, u.link)
        self.assertEqual(y, v.link)
        self.assertEqual(z, y.link)
        self.assertEqual(z, a.top_decision.value)

        a.backtrack(u)
        self.assertEqual(a.sentinel, a.top_decision.value)
        self.assertEqual(a.sentinel, a.sentinel.link)

    def test_conflict_clause(self):
        x = self.new_lit()
        y = self.new_lit()
        z = self.new_lit()
        a = Assignment(self.__mem, x, y, z)

        a.make_decision(x)
        a.make_decision(y)
        a.make_decision(z)
        c = self.new_clause(x, y, z)
        self.assertTrue(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

    def test_unit_clause(self):
        x = self.new_lit()
        y = self.new_lit()
        z = self.new_lit()
        a = Assignment(self.__mem, x, y, z)

        a.make_decision(x)
        a.make_decision(y)
        c = self.new_clause(z, x, y)
        self.assertFalse(c.is_conflict(a))
        self.assertEqual(z, c.derive(a))

    def test_binary_conflict_clause(self):
        x = self.new_lit()
        y = self.new_lit()
        a = Assignment(self.__mem, x, y)

        a.make_decision(x)
        a.make_decision(y)
        c = self.new_clause(x, y)
        self.assertTrue(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

    def test_binary_unit_clause(self):
        x = self.new_lit()
        y = self.new_lit()
        a = Assignment(self.__mem, x, y)

        a.make_decision(y)
        c = self.new_clause(x, y)
        self.assertFalse(c.is_conflict(a))
        self.assertEqual(x, c.derive(a))

    def test_trivial_conflict_clause(self):
        x = self.new_lit()
        a = Assignment(self.__mem, x)

        a.make_decision(x)
        c = self.new_clause(x)
        self.assertTrue(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

    def test_trivial_unit_clause(self):
        x = self.new_lit()
        a = Assignment(self.__mem, x)

        c = self.new_clause(x)
        self.assertFalse(c.is_conflict(a))
        self.assertEqual(x, c.derive(a))

    def test_update_to_conflict_v1(self):
        x = self.new_lit()
        y = self.new_lit()
        z = self.new_lit()
        a = Assignment(self.__mem, x, y, z)

        a.make_decision(x)
        c = self.new_clause(x, y, z)
        self.assertIsNone(a.get_suspicious_clause())
        self.assertFalse(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

        a.make_decision(y)
        self.assertEqual(c, a.get_suspicious_clause())
        self.assertIsNone(a.get_suspicious_clause())
        self.assertFalse(c.is_conflict(a))
        self.assertEqual(z, c.derive(a))

        a.make_decision(z)
        self.assertEqual(c, a.get_suspicious_clause())
        self.assertIsNone(a.get_suspicious_clause())
        self.assertTrue(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

    def test_update_to_conflict_v2(self):
        x = self.new_lit()
        y = self.new_lit()
        z = self.new_lit()
        a = Assignment(self.__mem, x, y, z)

        c = self.new_clause(x, y, z)
        self.assertIsNone(a.get_suspicious_clause())
        self.assertFalse(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

        a.make_decision(x)
        self.assertIsNone(a.get_suspicious_clause())
        self.assertFalse(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

        a.make_decision(y)
        self.assertEqual(c, a.get_suspicious_clause())
        self.assertIsNone(a.get_suspicious_clause())
        self.assertFalse(c.is_conflict(a))
        self.assertEqual(z, c.derive(a))

        a.make_decision(z)
        self.assertEqual(c, a.get_suspicious_clause())
        self.assertIsNone(a.get_suspicious_clause())
        self.assertTrue(c.is_conflict(a))
        self.assertIsNone(c.derive(a))

    def test_conflict_analysis_v1(self):
        x = self.new_lit()
        a = Assignment(self.__mem, x)

        a.make_decision(x)
        conflict = self.new_clause(x)
        self.assertTrue(conflict.is_conflict(a))

        self.assertEqual([x], a.analyze_conflict(conflict))

    def test_conflict_analysis_v2(self):
        x, y, z = self.new_lit(), self.new_lit(), self.new_lit()
        a = Assignment(self.__mem, x, y, z)

        a.make_decision(z)
        a.make_implication(x, self.new_clause(x.negated, z))
        a.make_implication(y, self.new_clause(y.negated, z))

        conflict = self.new_clause(x, y)
        self.assertTrue(conflict.is_conflict(a))

        self.assertEqual([z], a.analyze_conflict(conflict))

    def test_conflict_analysis_v3(self):
        u, v, x, y = self.new_lit(), self.new_lit(), self.new_lit(), self.new_lit()
        a = Assignment(self.__mem, u, v, x, y)

        a.make_decision(v)
        a.make_decision(y)
        a.make_implication(x, self.new_clause(x.negated, v, y))
        a.make_implication(u, self.new_clause(u.negated, v, x))

        conflict = self.new_clause(u)
        self.assertTrue(conflict.is_conflict(a))

        self.assertEqual([u], a.analyze_conflict(conflict))

    def test_conflict_analysis_v4(self):
        x1, x2, x3 = self.new_lit(), self.new_lit(), self.new_lit()
        x4, x5, x6 = self.new_lit(), self.new_lit(), self.new_lit()
        x7, x8, x9 = self.new_lit(), self.new_lit(), self.new_lit()
        a = Assignment(self.__mem, x1, x2, x3, x4, x5, x6, x7, x8, x9)

        a.make_decision(x1)
        a.make_implication(x5, self.new_clause(x5.negated, x1))
        a.make_decision(x6)
        a.make_decision(x9)
        a.make_implication(x8, self.new_clause(x8.negated, x9))
        a.make_implication(x7, self.new_clause(x7.negated, x6, x9, x8))
        a.make_implication(x4, self.new_clause(x4.negated, x7))
        a.make_implication(x2, self.new_clause(x2.negated, x4, x7))
        a.make_implication(x3, self.new_clause(x3.negated, x4, x5))

        conflict = self.new_clause(x1, x2, x3)
        self.assertTrue(conflict.is_conflict(a))

        self.assertEqual([x7, x5, x1], a.analyze_conflict(conflict))

    def test_dpll_steps(self):
        x1 = self.new_lit()
        x2 = self.new_lit()
        x3 = self.new_lit()
        x4 = self.new_lit()
        x5 = self.new_lit()
        x6 = self.new_lit()
        a = Assignment(self.__mem, x1, x2, x3, x4, x5, x6)

        c1 = self.new_clause(x1.negated, x2)
        c2 = self.new_clause(x3.negated, x4)
        c3 = self.new_clause(x5.negated, x6.negated)
        c4 = self.new_clause(x6, x5.negated, x2.negated)

        # DECIDE
        a.make_decision(x1.negated)

        # UNIT PROPAGATION
        self.assertEqual(c1, a.get_suspicious_clause())
        self.assertIsNone(a.get_suspicious_clause())
        self.assertEqual(x2, c1.derive(a))
        a.make_implication(x2.negated, c1)

        # DECIDE
        a.make_decision(x3.negated)

        # UNIT PROPAGATION
        self.assertEqual(c2, a.get_suspicious_clause())
        self.assertIsNone(a.get_suspicious_clause())
        self.assertEqual(x4, c2.derive(a))
        a.make_implication(x4.negated, c2)

        # DECIDE
        a.make_decision(x5.negated)

        # UNIT PROPAGATION
        self.assertEqual(c3, a.get_suspicious_clause())
        self.assertEqual(x6.negated, c3.derive(a))
        a.make_implication(x6, c3)

        # BACKJUMP & LEARN
        self.assertEqual(c4, a.get_suspicious_clause())
        self.assertTrue(c4.is_conflict(a))

        analysis = a.analyze_conflict(c4)
        self.assertEqual([x5.negated, x2.negated], analysis)
        c5 = self.new_clause(*analysis)

        self.assertEqual(x3.negated, analysis[1].link.link)
        a.backtrack(x3.negated)
        self.assertEqual(x5.negated, c5.derive(a))
        a.make_implication(x5, c5)

        # DECIDE
        a.make_decision(x3.negated)

        # UNIT PROPAGATION
        self.assertEqual(c2, a.get_suspicious_clause())
        self.assertIsNone(a.get_suspicious_clause())
        self.assertEqual(x4, c2.derive(a))
        a.make_implication(x4.negated, c2)

        # DECIDE
        a.make_decision(x6.negated)

        # verdict: SAT
        while True:
            c = a.get_suspicious_clause()
            if c is None:
                break
            self.assertFalse(c.is_conflict(a))
            self.assertIsNone(c.derive(a))

    def test_dpll_sat(self):
        x1 = self.new_lit()
        x2 = self.new_lit()
        x3 = self.new_lit()
        x4 = self.new_lit()
        x5 = self.new_lit()
        x6 = self.new_lit()
        xs = [x1, x2, x3, x4, x5, x6]

        f = {
            self.new_clause(x1.negated, x2),
            self.new_clause(x3.negated, x4),
            self.new_clause(x5.negated, x6.negated),
            self.new_clause(x6, x5.negated, x2.negated)
        }

        self.assertEqual(Status.SAT, self.__dpll(xs, f))

    def test_dpll_trivial_unsat(self):
        x1 = self.new_lit()
        xs = [x1]

        f = {
            self.new_clause(x1),
            self.new_clause(x1.negated)
        }

        self.assertEqual(Status.UNSAT, self.__dpll(xs, f))

    def test_dpll_unsat(self):
        x1 = self.new_lit()
        x2 = self.new_lit()
        x3 = self.new_lit()
        x4 = self.new_lit()
        xs = [x1, x2, x3, x4]

        f = {
            self.new_clause(x1.negated, x2),
            self.new_clause(x2.negated, x3),
            self.new_clause(x4.negated, x1),
            self.new_clause(x4.negated, x3.negated),
            self.new_clause(x4)
        }

        self.assertEqual(Status.UNSAT, self.__dpll(xs, f))

    def __dpll(self, xs: 'List[Literal]', f: 'Set[Clause]') -> 'Status':
        a = Assignment(self.__mem, *xs)
        while True:
            while True:
                clause = a.get_suspicious_clause()
                if clause is None:
                    break
                if clause.is_conflict(a):
                    literals = a.analyze_conflict(clause)
                    x = literals[0]
                    if len(literals) == 1:
                        if x.link == a.sentinel:
                            return Status.UNSAT
                        backtrack_lit = a.sentinel.link
                        if backtrack_lit != a.sentinel:
                            a.backtrack(backtrack_lit)
                    else:
                        y = literals[1]
                        backtrack_lit = y.link if y.antecedent is None else y.link.link
                        assert backtrack_lit != a.sentinel
                        a.backtrack(backtrack_lit)
                    asserting_clause = self.new_clause(*literals)
                    self.assertEqual(x, asserting_clause.derive(a))
                    a.make_implication(x.negated, asserting_clause)
                else:
                    z = clause.derive(a)
                    if z is not None:
                        a.make_implication(z.negated, clause)
            if a.border.value == len(xs)+1:
                break
            d = a.literals[a.border.value]
            a.make_decision(d.negated)

        self.assertTrue(all((a[x] is not None) for x in xs))
        for c in f:
            self.assertTrue(any((a[x.negated] is True) for x in c.literals))
        return Status.SAT


# -----------------------------------------------------------------------------
