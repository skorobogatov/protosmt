from typing import Optional, Tuple, List, Mapping, MutableMapping, Set, \
    Counter as CounterType, Callable, TypeVar, Generic
from typing_extensions import Protocol
from enum import Enum, auto
from abc import ABC, abstractmethod
from weakref import WeakValueDictionary
from collections import Counter

from smt.util import Unique


# -----------------------------------------------------------------------------


class Sort(Enum):
    UNKNOWN = auto()
    BOOL = auto()
    INT = auto()


class SortTrait(ABC):
    @property
    @abstractmethod
    def sort(self) -> 'Sort':
        pass


class BooleanMixin(SortTrait, ABC):
    @property
    def sort(self) -> 'Sort':
        return Sort.BOOL


class IntegerMixin(SortTrait, ABC):
    @property
    def sort(self) -> 'Sort':
        return Sort.INT


# -----------------------------------------------------------------------------


class ValencyTrait(ABC):
    def check_args(self, *args: 'Sort') -> 'bool':
        for i in range(len(args)):
            sort = args[i]
            if sort != Sort.UNKNOWN and self.get_arg_sort(i, True) != sort:
                return False
        return self.get_arg_sort(len(args), False) is None

    @abstractmethod
    def get_arg_sort(self, index: 'int', present: 'bool') -> 'Optional[Sort]':
        pass


class HomogeneousArgsTrait(ABC):
    @property
    @abstractmethod
    def arg_sort(self) -> 'Sort':
        pass


class BooleanArgsMixin(HomogeneousArgsTrait, ABC):
    @property
    def arg_sort(self) -> 'Sort':
        return Sort.BOOL


class IntegerArgsMixin(HomogeneousArgsTrait, ABC):
    @property
    def arg_sort(self) -> 'Sort':
        return Sort.INT


class NullaryValencyMixin(ValencyTrait, ABC):
    def get_arg_sort(self, index: 'int', present: 'bool') -> 'Optional[Sort]':
        return None


class UnaryValencyMixin(ValencyTrait, HomogeneousArgsTrait, ABC):
    def get_arg_sort(self, index: 'int', present: 'bool') -> 'Optional[Sort]':
        return self.arg_sort if index == 0 else None


class BinaryValencyMixin(ValencyTrait, HomogeneousArgsTrait, ABC):
    def get_arg_sort(self, index: 'int', present: 'bool') -> 'Optional[Sort]':
        return self.arg_sort if index == 0 or index == 1 else None


class MultiaryValencyMixin(ValencyTrait, HomogeneousArgsTrait, ABC):
    def get_arg_sort(self, index: 'int', present: 'bool') -> 'Optional[Sort]':
        return self.arg_sort if index == 0 or (index > 0 and present) else None


# -----------------------------------------------------------------------------


E = TypeVar('E')


Eval = Callable[['Expr', Tuple[E, ...]], E]


class Expr(Unique):
    @property
    @abstractmethod
    def symbol(self) -> 'Symbol':
        pass

    @property
    @abstractmethod
    def args(self) -> 'Tuple[Expr, ...]':
        pass

    @property
    @abstractmethod
    def negated(self) -> 'Expr':
        pass

    @property
    @abstractmethod
    def has_wrappers(self) -> 'bool':
        pass

    def bottom_up(self, visit: 'Callable[[Expr], None]') -> 'None':
        colors: 'CounterType[Expr]' = Counter()
        stack: 'List[Expr]' = [self]
        while len(stack) > 0:
            expr = stack.pop()
            color = colors[expr]
            if color == 0:
                stack.append(expr)
                stack.extend(reversed(expr.args))
                colors[expr] = 1
            elif color == 1:
                visit(expr)
                colors[expr] = 2

    def bottom_up_eval(self, ev: 'Eval[E]') -> 'E':
        values: 'MutableMapping[Expr, E]' = {}

        def visit(expr: 'Expr') -> 'None':
            values[expr] = ev(expr, tuple(values[π] for π in expr.args))

        self.bottom_up(visit)
        return values[self]

    def bottom_up_transform(self, transform: 'Eval[Expr]') -> 'Expr':
        def transform_wrapper(expr: 'Expr', values: 'Tuple[Expr, ...]') -> 'Expr':
            return transform(expr, values) if isinstance(expr.symbol, ValencySymbol) \
                else _ExprImpl(expr.symbol, values)

        return self.bottom_up_eval(transform_wrapper)

    def substitute(self, table: 'Mapping[Expr, Expr]') -> 'Expr':
        def transform(expr: 'Expr', values: 'Tuple[Expr, ...]') -> 'Expr':
            return table[expr] if expr in table else expr.symbol.apply(*values)

        return self.bottom_up_transform(transform)


@Unique.cached
class _ExprImpl(Expr):
    def __init__(self, symbol: 'Symbol', args: 'Tuple[Expr, ...]') -> 'None':
        self.__symbol, self.__args = symbol, args
        self.__has_wrappers = isinstance(symbol, WrapperSymbol) or any(π.has_wrappers for π in args)
        self.__negated = NegatorSymbol(symbol.sort).apply(self)

    @property
    def symbol(self) -> 'Symbol':
        return self.__symbol

    @property
    def args(self) -> 'Tuple[Expr, ...]':
        return self.__args

    @property
    def negated(self) -> 'Expr':
        return self.__negated

    @property
    def has_wrappers(self) -> 'bool':
        return self.__has_wrappers


# -----------------------------------------------------------------------------


class ReducerTrait(ABC):
    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        return None

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _negate(self, *args: 'Expr') -> 'Optional[Expr]':
        return None


class NullaryReducerMixin(ReducerTrait, ABC):
    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        assert len(args) == 0
        return self._nullary_reduce()

    def _negate(self, *args: 'Expr') -> 'Optional[Expr]':
        assert len(args) == 0
        return self._nullary_negate()

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _nullary_reduce(self) -> 'Optional[Expr]':
        return None

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _nullary_negate(self) -> 'Optional[Expr]':
        return None


class UnaryReducerMixin(ReducerTrait, ABC):
    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        assert len(args) == 1
        return self._unary_reduce(args[0])

    def _negate(self, *args: 'Expr') -> 'Optional[Expr]':
        assert len(args) == 1
        return self._unary_negate(args[0])

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _unary_reduce(self, a: 'Expr') -> 'Optional[Expr]':
        return None

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _unary_negate(self, a: 'Expr') -> 'Optional[Expr]':
        return None


class BinaryReducerMixin(ReducerTrait, ABC):
    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        assert len(args) == 2
        return self._binary_reduce(args[0], args[1])

    def _negate(self, *args: 'Expr') -> 'Optional[Expr]':
        assert len(args) == 2
        return self._binary_negate(args[0], args[1])

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _binary_reduce(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
        return None

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _binary_negate(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
        return None


# -----------------------------------------------------------------------------


class Symbol(Unique, SortTrait):
    @abstractmethod
    def apply(self, *args: 'Expr') -> 'Expr':
        pass


class WrapperSymbol(Symbol):
    def __init__(self, opt_symbol: 'Optional[ValencySymbol]' = None) -> 'None':
        self.__opt_symbol = opt_symbol

    @property
    def opt_symbol(self) -> 'Optional[ValencySymbol]':
        return self.__opt_symbol

    @property
    def sort(self) -> 'Sort':
        opt_symbol = self.opt_symbol
        return Sort.UNKNOWN if opt_symbol is None else opt_symbol.sort

    def apply(self, *args: 'Expr') -> 'Expr':
        return _ExprImpl(self, args)


class ValencySymbol(Symbol, ValencyTrait, ReducerTrait, ABC):
    __applications_cache: 'MutableMapping[Tuple[ValencySymbol, Tuple[Expr, ...]], Expr]' = \
        WeakValueDictionary()

    def apply(self, *args: 'Expr') -> 'Expr':
        if not self.check_args(*(π.symbol.sort for π in args)):
            return WrapperSymbol(self).apply(*args)
        key = (self, args)
        expr = ValencySymbol.__applications_cache.get(key)
        if expr is None:
            expr = self._reduce(*args)
            if expr is None:
                ValencySymbol.__applications_cache[key] = expr = _ExprImpl(self, args)
        return expr


# -----------------------------------------------------------------------------


class CustomSymbol(ValencySymbol, ABC):
    def __init__(self, sort: 'Sort') -> 'None':
        self.__sort = sort

    @property
    def sort(self) -> 'Sort':
        return self.__sort


@Unique.priority(0)
@Unique.cached
class NegatorSymbol(CustomSymbol, UnaryValencyMixin, UnaryReducerMixin):
    @property
    def arg_sort(self) -> 'Sort':
        return self.sort

    def _unary_reduce(self, a: 'Expr') -> 'Optional[Expr]':
        sym = a.symbol
        if isinstance(sym, ValencySymbol):
            e = sym._negate(*a.args)
            if e is not None:
                return e
        return _ExprImpl(self, (a,))

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _unary_negate(self, a: 'Expr') -> 'Optional[Expr]':
        return a


# -----------------------------------------------------------------------------


@Unique.priority(2)
class VariableSymbol(CustomSymbol, NullaryValencyMixin):
    pass


@Unique.priority(3)
class FunctionSymbol(CustomSymbol):
    def __init__(self,
                 sort: 'Sort',
                 args: 'Tuple[Sort, ...]') -> 'None':
        super().__init__(sort)
        self.__args = args

    @property
    def args(self) -> 'Tuple[Sort, ...]':
        return self.__args

    def get_arg_sort(self, index: 'int', present: 'bool') -> 'Optional[Sort]':
        return self.args[index] if 0 <= index < len(self.args) else None


@Unique.priority(4)
@Unique.cached
class MacroSymbol(FunctionSymbol):
    def __init__(self,
                 sort: 'Sort',
                 formal_args: 'Tuple[VariableSymbol, ...]',
                 body: 'Expr') -> 'None':
        super().__init__(sort, tuple(π.sort for π in formal_args))
        self.__formal_args, self.__body = formal_args, body

    @property
    def formal_args(self) -> 'Tuple[VariableSymbol, ...]':
        return self.__formal_args

    @property
    def body(self) -> 'Expr':
        return self.__body

    def _reduce(self, *args: 'Expr') -> 'Optional[Expr]':
        if isinstance(self.body.symbol, ValencySymbol) and (self.body.symbol.sort == self.sort):
            table = {self.formal_args[i].apply(): args[i] for i in range(len(args))}
            return self.body.substitute(table)
        return None


# -----------------------------------------------------------------------------


class AssociativeCommutativeSymbol(ValencySymbol, MultiaryValencyMixin, ABC):
    def __init__(self) -> 'None':
        assert self.sort == self.get_arg_sort(0, True)

    def _reduce(self, *args: 'Expr') -> 'Expr':
        index_to_expr: 'List[Expr]' = []

        def flatten(*es: 'Expr') -> 'Set[int]':
            dest: 'Set[int]' = set()
            stack: 'List[Expr]' = list(es)
            while len(stack) > 0:
                e = stack.pop()
                if e.symbol == self:
                    stack.extend(e.args)
                else:
                    index = len(index_to_expr)
                    index_to_expr.append(e)
                    dest.add(index)
            return dest

        res: 'Set[int]' = flatten(*args)
        res_copy = res.copy()
        tasks: 'List[Tuple[Set[int], Set[int]]]' = [(res_copy, res_copy)]
        while len(tasks) > 0:
            (first, second) = tasks.pop()
            second_list = [i for i in second if i in res]
            created: 'Set[int]' = set()
            for a in first:
                if a in res:
                    for i in range(len(second_list)):
                        b = second_list[i]
                        if (a != b) and (b in res):
                            c = self._binary_reduce(index_to_expr[a], index_to_expr[b])
                            if c is not None:
                                res.remove(a)
                                res.remove(b)
                                created |= flatten(c)
                                second_list[i] = second_list[-1]
                                second_list.pop()
                                break
            if len(created) > 0:
                res_copy = res.copy()
                tasks.append((res_copy, created))
                tasks.append((created, res_copy))
                tasks.append((created, created))
                res |= created

        new_args = tuple(sorted(index_to_expr[i] for i in res))
        return new_args[0] if len(res) == 1 and isinstance(new_args[0].symbol, ValencySymbol) \
            else _ExprImpl(self, new_args)

    # noinspection PyMethodMayBeStatic,PyUnusedLocal
    def _binary_reduce(self, a: 'Expr', b: 'Expr') -> 'Optional[Expr]':
        return None


class __HasLt(Protocol):
    @abstractmethod
    def __lt__(self, other) -> 'bool':
        pass


T = TypeVar('T', bound=__HasLt)


class ConstSymbol(Generic[T], ValencySymbol, NullaryValencyMixin, NullaryReducerMixin, ABC):
    def __init__(self, value: 'T') -> 'None':
        self.__value = value

    @property
    def value(self) -> T:
        return self.__value


# -----------------------------------------------------------------------------
