from typing import Optional, Tuple, Mapping, cast
from unittest import TestCase


from smt.logic.symbols_base import Sort, \
    NullaryValencyMixin, UnaryValencyMixin, BinaryValencyMixin, MultiaryValencyMixin, \
    BooleanArgsMixin, IntegerArgsMixin, IntegerMixin, Expr, \
    ValencySymbol, WrapperSymbol, NegatorSymbol, AssociativeCommutativeSymbol, VariableSymbol
from smt.logic.builtin_symbols import IntegerConstSymbol, integer, integer_sum, \
    boolean, boolean_and, boolean_or, boolean_implies, boolean_eq, integer_eq


# -----------------------------------------------------------------------------


class TestValency(TestCase):
    class A(NullaryValencyMixin):
        pass

    def test_nullary_valency(self):
        a = TestValency.A()
        self.assertFalse(a.check_args(Sort.INT))
        self.assertFalse(a.check_args(Sort.BOOL))
        self.assertFalse(a.check_args(Sort.INT, Sort.INT))
        self.assertFalse(a.check_args(Sort.BOOL, Sort.BOOL))
        self.assertFalse(a.check_args(Sort.BOOL, Sort.INT))
        self.assertTrue(a.check_args())

    class B(UnaryValencyMixin, BooleanArgsMixin):
        pass

    def test_unary_valency(self):
        b = TestValency.B()
        self.assertFalse(b.check_args(Sort.INT))
        self.assertTrue(b.check_args(Sort.BOOL))
        self.assertTrue(b.check_args(Sort.UNKNOWN))
        self.assertFalse(b.check_args(Sort.INT, Sort.INT))
        self.assertFalse(b.check_args(Sort.BOOL, Sort.BOOL))
        self.assertFalse(b.check_args(Sort.BOOL, Sort.INT))
        self.assertFalse(b.check_args())

    class C(BinaryValencyMixin, IntegerArgsMixin):
        pass

    def test_binary_valency(self):
        c = TestValency.C()
        self.assertFalse(c.check_args(Sort.INT))
        self.assertFalse(c.check_args(Sort.BOOL))
        self.assertTrue(c.check_args(Sort.INT, Sort.INT))
        self.assertTrue(c.check_args(Sort.UNKNOWN, Sort.INT))
        self.assertTrue(c.check_args(Sort.INT, Sort.UNKNOWN))
        self.assertFalse(c.check_args(Sort.BOOL, Sort.BOOL))
        self.assertFalse(c.check_args(Sort.BOOL, Sort.INT))
        self.assertFalse(c.check_args())

    class D(MultiaryValencyMixin, BooleanArgsMixin):
        pass

    def test_multiary_valency(self):
        d = TestValency.D()
        self.assertFalse(d.check_args(Sort.INT))
        self.assertTrue(d.check_args(Sort.BOOL))
        self.assertTrue(d.check_args(Sort.UNKNOWN))
        self.assertFalse(d.check_args(Sort.INT, Sort.INT))
        self.assertTrue(d.check_args(Sort.BOOL, Sort.BOOL))
        self.assertTrue(d.check_args(Sort.UNKNOWN, Sort.BOOL))
        self.assertTrue(d.check_args(Sort.BOOL, Sort.UNKNOWN))
        self.assertFalse(d.check_args(Sort.BOOL, Sort.INT))
        self.assertTrue(d.check_args(Sort.BOOL, Sort.BOOL, Sort.BOOL))
        self.assertTrue(d.check_args(Sort.UNKNOWN, Sort.BOOL, Sort.UNKNOWN))
        self.assertFalse(d.check_args())


# -----------------------------------------------------------------------------


class TestExpr(TestCase):
    class A(ValencySymbol, NullaryValencyMixin, IntegerMixin):
        def __init__(self, value: 'int'):
            self.__value = value

        @property
        def value(self) -> 'int':
            return self.__value

        def __repr__(self) -> 'str':
            return f"A({self.value})"

    class B(ValencySymbol, BinaryValencyMixin, IntegerMixin, IntegerArgsMixin):
        def __repr__(self) -> 'str':
            return "B"

    def test_create_expr(self):
        a = TestExpr.A(10)
        e1 = a.apply()
        self.assertEqual(a, e1.symbol)
        self.assertEqual(0, len(e1.args))

        b = TestExpr.B()
        e2 = b.apply(e1, e1)
        e3 = b.apply(e1, e1)
        self.assertFalse(e2.has_wrappers)
        self.assertEqual(b, e2.symbol)
        self.assertEqual(2, len(e2.args))
        self.assertIs(e2, e3)
        self.assertEqual(e2, e3)

        e4 = b.apply(e1)
        e5 = b.apply(e1)
        self.assertTrue(e4.has_wrappers)
        self.assertIsInstance(e4.symbol, WrapperSymbol)
        self.assertEqual(b, cast(WrapperSymbol, e4.symbol).opt_symbol)
        self.assertEqual(1, len(e4.args))
        self.assertNotEqual(e4, e5)

    def test_negation(self):
        a = TestExpr.A(10)
        e = a.apply()
        self.assertIsInstance(e.negated.symbol, NegatorSymbol)
        self.assertEqual(e, e.negated.args[0])
        self.assertEqual(e, e.negated.negated)

    def test_bottom_up(self):
        x, y, z = TestExpr.A(1), TestExpr.A(2), TestExpr.A(3)
        b = TestExpr.B()
        f = b.apply(x.apply(), y.apply())
        e = b.apply(f, b.apply(z.apply(), f))

        count = [0]

        def add(expr: 'Expr', args: 'Tuple[int, ...]') -> 'int':
            sym = expr.symbol
            if isinstance(sym, TestExpr.A):
                return sym.value
            if isinstance(sym, TestExpr.B):
                count[0] += 1
                return args[0] + args[1]
            assert False, "we should not be here!"

        s = e.bottom_up_eval(add)
        self.assertEqual(9, s)
        self.assertEqual(3, count[0])

    def test_substitute(self):
        u, v, x, y, z = TestExpr.A(10), TestExpr.A(20), TestExpr.A(1), TestExpr.A(2), TestExpr.A(3)
        b = TestExpr.B()
        f = b.apply(v.apply(), v.apply())
        e = b.apply(
            b.apply(f, f),
            b.apply(
                b.apply(u.apply(), v.apply()),
                b.apply(
                    b.apply(x.apply(), y.apply()),
                    z.apply()
                )
            )
        )
        table: 'Mapping[Expr, Expr]' = {
            f: u.apply(),
            u.apply(): z.apply()
        }
        e2 = b.apply(
            b.apply(u.apply(), u.apply()),
            b.apply(
                b.apply(z.apply(), v.apply()),
                b.apply(
                    b.apply(x.apply(), y.apply()),
                    z.apply()
                )
            )
        )
        e3 = e.substitute(table)
        self.assertEqual(e2, e3)


class TestReducers(TestCase):
    class Op(AssociativeCommutativeSymbol, IntegerMixin, IntegerArgsMixin):
        def _binary_reduce(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
            a_sym, b_sym = a.symbol, b.symbol
            if a == b.negated:
                return integer(0)
            if isinstance(a_sym, IntegerConstSymbol) and isinstance(b_sym, IntegerConstSymbol):
                if a_sym.value == 0:
                    return b
            return None

    def test_commutativity(self):
        zero, x = integer(0), integer(-10)
        op = TestReducers.Op()

        e1 = op.apply(zero, x)
        self.assertEqual(integer(-10), e1)

        e2 = op.apply(x, zero)
        self.assertEqual(integer(-10), e2)

    def test_flattening(self):
        x, y, z, u, v = integer(1), integer(2), integer(3), integer(4), integer(5)
        op = TestReducers.Op()
        e = op.apply(
            op.apply(op.apply(u, v), z),
            op.apply(x, y)
        )
        self.assertIsInstance(e.symbol, TestReducers.Op)
        self.assertEqual(5, len(e.args))
        self.assertEqual(1, cast(IntegerConstSymbol, e.args[0].symbol).value)
        self.assertEqual(2, cast(IntegerConstSymbol, e.args[1].symbol).value)
        self.assertEqual(3, cast(IntegerConstSymbol, e.args[2].symbol).value)
        self.assertEqual(4, cast(IntegerConstSymbol, e.args[3].symbol).value)
        self.assertEqual(5, cast(IntegerConstSymbol, e.args[4].symbol).value)

    def test_associativity_commutativity(self):
        x, y, z = integer(-1), integer(2), integer(1)
        op = TestReducers.Op()
        e = op.apply(x, y, z)
        self.assertIsInstance(e.symbol, IntegerConstSymbol)
        self.assertEqual(2, cast(IntegerConstSymbol, e.symbol).value)

    def test_repeated_args(self):
        x = integer(1)
        op = TestReducers.Op()
        e = op.apply(x, x)
        self.assertIsInstance(e.symbol, TestReducers.Op)
        self.assertEqual(2, len(e.args))
        self.assertEqual(x, e.args[0])
        self.assertEqual(x, e.args[1])


# -----------------------------------------------------------------------------


class TestBuiltins(TestCase):
    def test_basic_identities(self):
        a = VariableSymbol(Sort.BOOL).apply()
        b = VariableSymbol(Sort.BOOL).apply()
        c = VariableSymbol(Sort.BOOL).apply()
        self.assertEqual(boolean_or(a, b),
                         boolean_or(b, a))
        self.assertEqual(boolean_and(a, b),
                         boolean_and(a, b))
        self.assertEqual(boolean_or(boolean_or(a, b), c),
                         boolean_or(a, boolean_or(b, c)))
        self.assertEqual(boolean_and(boolean_and(a, b), c),
                         boolean_and(a, boolean_and(b, c)))
        self.assertEqual(boolean_or(a, b).negated,
                         boolean_and(a.negated, b.negated))
        self.assertEqual(boolean_and(a, b).negated,
                         boolean_or(a.negated, b.negated))
        self.assertEqual(boolean_or(a, a), a)
        self.assertEqual(boolean_and(a, a), a)
        self.assertEqual(boolean_or(a, a.negated), boolean(True))
        self.assertEqual(boolean_and(a, a.negated), boolean(False))
        self.assertEqual(boolean_or(a, boolean(True)), boolean(True))
        self.assertEqual(boolean_or(a, boolean(False)), a)
        self.assertEqual(boolean_and(a, boolean(True)), a)
        self.assertEqual(boolean_and(a, boolean(False)), boolean(False))
        self.assertEqual(boolean_or(a, boolean_and(a, b)), a)
        self.assertEqual(boolean_and(a, boolean_or(a, b)), a)
        self.assertEqual(boolean_or(boolean_and(a, b), boolean_and(a.negated, b)), b)
        self.assertEqual(boolean_and(boolean_or(a, b), boolean_or(a.negated, b)), b)
        self.assertEqual(boolean_or(boolean_and(a, b), a.negated),
                         boolean_or(a.negated, b))
        self.assertEqual(boolean_and(boolean_or(a, b), a.negated),
                         boolean_and(a.negated, b))
        self.assertEqual(boolean_implies(a, b),
                         boolean_implies(b.negated, a.negated))
        self.assertEqual(a.negated.negated, a)
        self.assertEqual(boolean_eq(a, b),
                         boolean_and(boolean_implies(a, b), boolean_implies(b, a)))

    def test_boolean_eq(self):
        a = VariableSymbol(Sort.BOOL).apply()
        b = VariableSymbol(Sort.BOOL).apply()
        c = VariableSymbol(Sort.BOOL).apply()
        self.assertEqual(boolean_eq(a, a, a, a), boolean(True))
        self.assertEqual(boolean_eq(b, a, a), boolean_eq(a, b))
        self.assertEqual(boolean_eq(a, b, c),
                         boolean_and(boolean_eq(a, b), boolean_eq(b, c)))

    def test_integer_eq(self):
        a = VariableSymbol(Sort.INT).apply()
        b = VariableSymbol(Sort.INT).apply()
        c = VariableSymbol(Sort.INT).apply()
        self.assertEqual(integer_eq(a, a, a, a), boolean(True))
        self.assertEqual(integer_eq(a, b, c), integer_eq(a, b, c))
        self.assertEqual(integer_eq(b, a, a, c, c), integer_eq(a, b, c))

    def test_sum(self):
        e = integer_sum(
            integer_sum(
                integer_sum(
                    integer_sum(
                        integer_sum(integer(1), integer(2)),
                        integer_sum(integer(3), integer(4), integer(5))
                    ),
                    integer_sum(integer(6), integer(7))
                ),
                integer_sum(integer(8), integer(9), integer(10))
            ),
            integer_sum(
                integer_sum(integer(11), integer(12)),
                integer_sum(integer(13), integer(14)),
                integer_sum(integer(15), integer(16))
            ),
            integer_sum(
                integer_sum(integer(17), integer(18)),
                integer_sum(integer(19), integer(20))
            )
        )
        self.assertEqual(e.negated, integer(-210))

    def test_homogeneous_sum(self):
        a = integer(10)
        e = integer_sum(a, a, integer_sum(a, integer_sum(a, a), a))
        self.assertEqual(e, integer(60))


# -----------------------------------------------------------------------------
