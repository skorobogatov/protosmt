from typing import Optional, Tuple, Set

from smt.util import Unique
from smt.logic.symbols_base import Sort, BooleanMixin, IntegerMixin, \
    BooleanArgsMixin, IntegerArgsMixin, BinaryValencyMixin, MultiaryValencyMixin, \
    Expr, BinaryReducerMixin, \
    ValencySymbol, VariableSymbol, AssociativeCommutativeSymbol, ConstSymbol


# -----------------------------------------------------------------------------


@Unique.priority(1)
@Unique.cached
class BooleanConstSymbol(ConstSymbol[bool], BooleanMixin):
    def _nullary_negate(self) -> 'Optional[Expr]':
        return boolean(not self.value)


@Unique.cached
class BooleanConnectiveSymbol(AssociativeCommutativeSymbol,
                              BooleanMixin, BooleanArgsMixin):
    def __init__(self, neutral_elem: 'bool'):
        super().__init__()
        self.__neutral_elem = neutral_elem
        self.__zero, self.__one = boolean(neutral_elem), boolean(not neutral_elem)

    @property
    def neutral_elem(self) -> 'bool':
        return self.__neutral_elem

    def _binary_reduce(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
        if a == b:
            return a
        if a == b.negated:
            return self.__one
        if a == self.__zero:
            return b
        if a == self.__one:
            return a

        opposite = self.__opposite
        if b.symbol == opposite:
            b_args: 'Set[Expr]' = set(b.args)
            if a.negated in b_args:
                return self.apply(a, *(b_args - {a.negated}))
            a_args: 'Set[Expr]' = set(a.args) if a.symbol == opposite else {a}
            if a_args <= b_args:
                return a
            common = a_args & b_args
            if len(common) > 0:
                if opposite.apply(*(a_args - common)) == opposite.apply(*(b_args - common)).negated:
                    return opposite.apply(*common)

        return None

    def _negate(self, *args: 'Expr') -> 'Optional[Expr]':
        return self.__opposite.apply(*(π.negated for π in args))

    @property
    def __opposite(self) -> 'BooleanConnectiveSymbol':
        return BooleanConnectiveSymbol(not self.neutral_elem)


@Unique.cached
class BooleanImplicationSymbol(ValencySymbol, BinaryValencyMixin, BinaryReducerMixin,
                               BooleanMixin, BooleanArgsMixin):
    def _binary_reduce(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
        return boolean_or(a.negated, b)


@Unique.cached
class BooleanEqSymbol(ValencySymbol, MultiaryValencyMixin, BooleanMixin, BooleanArgsMixin):
    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        es: 'Set[Expr]' = set(args)
        if len(es) == 1:
            return boolean(True)
        new_args = tuple(sorted(es))
        if len(es) == 2:
            a, b = new_args
            return boolean_and(boolean_or(a.negated, b), boolean_or(a, b.negated))
        return boolean_and(*(boolean_eq(*new_args[i: i+2]) for i in range(len(es)-1)))


@Unique.cached
class IntegerEqSymbol(ValencySymbol, MultiaryValencyMixin, BooleanMixin, IntegerArgsMixin):
    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        es: 'Set[Expr]' = set(args)
        if len(es) == 1:
            return boolean(True)
        if any(ε.symbol == IntegerSumSymbol() for ε in es):
            sums = [set(ε.args) if ε.symbol == IntegerSumSymbol() else {ε} for ε in es]
            common = set.intersection(*sums)
            if len(common) > 0:
                new_args = []
                for π in sums:
                    π -= common
                    if len(π) == 0:
                        new_args.append(integer(0))
                    elif len(π) == 1:
                        new_args.append(π.pop())
                    else:
                        new_args.append(integer_sum(*π))
                return integer_eq(*new_args)
        if (len(es) < len(args)) or any(args[i] > args[i+1] for i in range(len(args)-1)):
            return integer_eq(*sorted(es))
        return None


@Unique.cached
class BooleanXorSymbol(ValencySymbol, MultiaryValencyMixin,
                       BooleanMixin, BooleanArgsMixin):
    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        return boolean_and(boolean_or(*args), boolean_and(*args).negated)  # TODO: probably bullshit!


# -----------------------------------------------------------------------------


@Unique.priority(1)
@Unique.cached
class IntegerConstSymbol(ConstSymbol[int], IntegerMixin):
    def _nullary_negate(self) -> 'Optional[Expr]':
        return integer(-self.value)


@Unique.cached
class IntegerSumSymbol(AssociativeCommutativeSymbol,
                       IntegerMixin, IntegerArgsMixin):
    def _binary_reduce(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
        a_sym, b_sym = a.symbol, b.symbol
        if a == b.negated:
            return integer(0)
        if a == integer(0):
            return b
        if isinstance(a_sym, IntegerConstSymbol) and isinstance(b_sym, IntegerConstSymbol):
            return integer(a_sym.value + b_sym.value)
        return None

    def _negate(self, *args: 'Expr') -> 'Optional[Expr]':
        return integer_sum(*(π.negated for π in args))


@Unique.cached
class IntegerDiffSymbol(ValencySymbol, BinaryValencyMixin, BinaryReducerMixin,
                        IntegerMixin, IntegerArgsMixin):
    def _binary_reduce(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
        return integer_sum(a, b.negated)


# -----------------------------------------------------------------------------


def boolean(value: 'bool') -> 'Expr':
    return BooleanConstSymbol(value).apply()


def boolean_and(*args: 'Expr') -> 'Expr':
    return BooleanConnectiveSymbol(True).apply(*args)


def boolean_or(*args: 'Expr') -> 'Expr':
    return BooleanConnectiveSymbol(False).apply(*args)


def boolean_implies(a: 'Expr', b: 'Expr') -> 'Expr':
    return BooleanImplicationSymbol().apply(a, b)


def boolean_eq(*args: 'Expr') -> 'Expr':
    return BooleanEqSymbol().apply(*args)


def integer_eq(*args: 'Expr') -> 'Expr':
    return IntegerEqSymbol().apply(*args)


def integer(value: 'int') -> 'Expr':
    return IntegerConstSymbol(value).apply()


def integer_sum(*args: 'Expr') -> 'Expr':
    return IntegerSumSymbol().apply(*args)


def integer_diff(a: 'Expr', b: 'Expr') -> 'Expr':
    return IntegerDiffSymbol().apply(a, b)


# -----------------------------------------------------------------------------


@Unique.priority(2)
@Unique.cached
class TseitinVarSymbol(VariableSymbol):
    def __init__(self, expr: 'Expr'):
        assert expr.symbol.sort == Sort.BOOL
        super().__init__(Sort.BOOL)


def to_cnf(expr: 'Expr') -> 'Expr':
    assert expr.symbol.sort == Sort.BOOL
    eqs: 'Set[Expr]' = set()

    def transform(e: 'Expr', args: 'Tuple[Expr, ...]') -> 'Expr':
        w = e.symbol.apply(*args)
        sym = w.symbol
        if isinstance(sym, BooleanConnectiveSymbol) and e != expr:
            w = TseitinVarSymbol(w).apply()
            if sym.neutral_elem:
                eqs.add(boolean_implies(boolean_and(*args), w))
                eqs.update(boolean_implies(w, π) for π in args)
            else:
                eqs.add(boolean_implies(w, boolean_or(*args)))
                eqs.update(boolean_implies(π, w) for π in args)
        return w

    return boolean_and(expr.bottom_up_transform(transform), *eqs)


# -----------------------------------------------------------------------------
