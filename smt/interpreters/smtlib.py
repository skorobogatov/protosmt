from typing import Union, Optional, Tuple, List, Mapping, MutableMapping, \
    Set, MutableSet, Iterator, Type, cast
from collections.abc import Sequence
from dataclasses import dataclass
from enum import Enum, auto
import re

from smt.util import Memory, TransactionalMapping, TransactionalSet
from smt.logic import Sort, Expr, Symbol, ValencySymbol, WrapperSymbol, \
    NegatorSymbol, VariableSymbol, FunctionSymbol, MacroSymbol, \
    boolean, BooleanConstSymbol, BooleanConnectiveSymbol, \
    BooleanImplicationSymbol, BooleanEqSymbol, \
    integer, IntegerEqSymbol, IntegerSumSymbol, IntegerDiffSymbol, \
    boolean_and, TseitinVarSymbol, to_cnf, \
    Model, Status
from smt.interpreters.scanner_base import Position, Message, MessageSet, AbstractScanner
from smt.interpreters.parser_base import Node, SequenceNode, VoidVisitor


# -----------------------------------------------------------------------------


class Tag(Enum):
    LEFT_PAREN = auto()
    RIGHT_PAREN = auto()
    IDENT = auto()
    NUMBER = auto()
    BOOL = auto()
    INT = auto()
    ASSERT = auto()
    CHECK_SAT = auto()
    DECLARE_CONST = auto()
    DECLARE_FUN = auto()
    DEFINE_FUN = auto()
    GET_MODEL = auto()
    SIMPLIFY = auto()
    LET = auto()

    def __str__(self) -> 'str':
        return f"'{_tag_labels[self]}'"


_tag_labels: 'Mapping[Tag, str]' = {
    Tag.LEFT_PAREN: '(',
    Tag.RIGHT_PAREN: ')',
    Tag.IDENT: 'identifier',
    Tag.NUMBER: 'number',
    Tag.BOOL: 'Bool',
    Tag.INT: 'Int',
    Tag.ASSERT: 'assert',
    Tag.CHECK_SAT: 'check-sat',
    Tag.DECLARE_CONST: 'declare-const',
    Tag.DECLARE_FUN: 'declare-fun',
    Tag.DEFINE_FUN: 'define-fun',
    Tag.SIMPLIFY: 'simplify',
    Tag.LET: 'let'
}


class Scanner(AbstractScanner[Tag]):
    __KEYWORDS: 'Mapping[str, Tag]' = {
        'Bool': Tag.BOOL,
        'Int': Tag.INT,
        'assert': Tag.ASSERT,
        'check-sat': Tag.CHECK_SAT,
        'declare-const': Tag.DECLARE_CONST,
        'declare-fun': Tag.DECLARE_FUN,
        'define-fun': Tag.DEFINE_FUN,
        'get-model': Tag.GET_MODEL,
        'simplify': Tag.SIMPLIFY,
        'let': Tag.LET,
    }

    __PARENTHESES: 'Mapping[str, Tag]' = {
        '(': Tag.LEFT_PAREN,
        ')': Tag.RIGHT_PAREN,
    }

    __NON_DIGIT = r'a-zA-Z+\-/*=%?!.$_~&\^<>@'
    __SYM_START = re.compile(r'[%s]' % __NON_DIGIT)
    __SYM_FOLLOW = re.compile(r'[%s0-9]' % __NON_DIGIT)

    def _scan(self) -> 'Optional[Tag]':
        while True:
            self._consume_while(str.isspace)
            self._mark_start()
            if self._consume(';'):
                self._consume_until('\n')
            elif self._consume(lambda ch: ch in Scanner.__PARENTHESES):
                return Scanner.__PARENTHESES[self.image]
            elif self._consume(Scanner.__SYM_START.match):
                self._consume_while(Scanner.__SYM_FOLLOW.match)
                return Scanner.__KEYWORDS.get(self.image, Tag.IDENT)
            elif self._consume(str.isdecimal):
                self._consume_while(str.isdecimal)
                return Tag.NUMBER
            elif self._consume(Position.EOF):
                return None
            else:
                self._consume_invalid_char()


# -----------------------------------------------------------------------------


class AssertNode(Node[Tag]):
    """
    assert = ASSERT term.
    """

    term: 'TermNode'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.ASSERT)
        self._next()
        self.term = TermNode(self)


class CheckSatNode(Node[Tag]):
    """
    check-sat = CHECK_SAT.
    """

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.CHECK_SAT)
        self._next()


class DeclareConstNode(Node[Tag]):
    """
    declare-const = DECLARE_CONST ident sort.
    """

    ident: 'IdentNode'
    sort: 'SortNode'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.DECLARE_CONST)
        self._next()
        self.ident = IdentNode(self)
        self.sort = SortNode(self)


class DeclareFunNode(Node[Tag]):
    """
    declare-fun = DECLARE_FUN ident sort-list sort.
    """

    ident: 'IdentNode'
    args: 'Sequence[SortNode]'
    sort: 'SortNode'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.DECLARE_FUN)
        self._next()
        self.ident = IdentNode(self)
        self.args = SortListNode(self)
        self.sort = SortNode(self)


class DefineFunNode(Node[Tag]):
    """
    define-fun = DEFINE_FUN ident sorted-var-list sort term.
    """

    ident: 'IdentNode'
    args: 'Sequence[SortedVarNode]'
    sort: 'SortNode'
    term: 'TermNode'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.DEFINE_FUN)
        self._next()
        self.ident = IdentNode(self)
        self.args = SortedVarListNode(self)
        self.sort = SortNode(self)
        self.term = TermNode(self)


class GetModelNode(Node[Tag]):
    """
    get-model = GET_MODEL.
    """

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.GET_MODEL)
        self._next()


class SimplifyNode(Node[Tag]):
    """
    simplify = SIMPLIFY term.
    """

    term: 'TermNode'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.SIMPLIFY)
        self._next()
        self.term = TermNode(self)


class CommandNode(Node[Tag]):
    """
    command
        = LEFT_PAREN command-content RIGHT_PAREN.
    command-content
        = assert
        | check-sat
        | declare-const
        | declare-fun
        | define-fun
        | get-model
        | simplify.
    """

    CommandType = Union[AssertNode, CheckSatNode, DeclareConstNode,
                        DeclareFunNode, DefineFunNode, GetModelNode,
                        SimplifyNode]

    content: 'CommandType'

    __DISPATCH: 'Mapping[Tag, Type[CommandType]]' = {
        Tag.ASSERT: AssertNode,
        Tag.CHECK_SAT: CheckSatNode,
        Tag.DECLARE_CONST: DeclareConstNode,
        Tag.DECLARE_FUN: DeclareFunNode,
        Tag.DEFINE_FUN: DefineFunNode,
        Tag.GET_MODEL: GetModelNode,
        Tag.SIMPLIFY: SimplifyNode
    }

    @Node.recover(following={Tag.LEFT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.LEFT_PAREN)
        self._next()
        tag = self._expect(*CommandNode.__DISPATCH.keys())
        node_cls = CommandNode.__DISPATCH[tag]
        self.content = node_cls(self)
        self._expect(Tag.RIGHT_PAREN)
        self._next()


class CommandListNode(SequenceNode[Tag, CommandNode]):
    """
    command-list = { command }.
    """

    def _parse_seq(self) -> 'None':
        while self._match(Tag.LEFT_PAREN):
            self._append(CommandNode(self))


class TermNode(Node[Tag]):
    """
    term
        = ident
        | number
        | LEFT_PAREN expr RIGHT_PAREN.
    expr
        = call-expr
        | let-expr.
    """

    content: 'Union[IdentNode, NumberNode, LetExprNode, CallExprNode]'

    @Node.recover(following={Tag.LEFT_PAREN, Tag.IDENT, Tag.NUMBER, Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        tag = self._expect(Tag.IDENT, Tag.NUMBER, Tag.LEFT_PAREN)
        if tag == Tag.IDENT:
            self.content = IdentNode(self)
        elif tag == Tag.NUMBER:
            self.content = NumberNode(self)
        else:
            self._next()
            self.content = LetExprNode(self) if self._match(Tag.LET) else CallExprNode(self)
            self._expect(Tag.RIGHT_PAREN)
            self._next()


class TermListNode(SequenceNode[Tag, TermNode]):
    """
    term-list = term { term }.
    """

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse_seq(self) -> 'None':
        self._append(TermNode(self))
        while self._match(Tag.IDENT, Tag.NUMBER, Tag.LEFT_PAREN):
            self._append(TermNode(self))


class CallExprNode(Node[Tag]):
    """
    call-expr = ident term-list.
    """

    ident: 'IdentNode'
    args: 'Sequence[TermNode]'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self.ident = IdentNode(self)
        if self._match(Tag.LEFT_PAREN, Tag.IDENT, Tag.NUMBER):
            self.args = TermListNode(self)
        else:
            self._report_raise("invalid function application, arguments missing")


class LetExprNode(Node[Tag]):
    """
    let-expr = LET var-binding-list term.
    """

    bindings: 'Sequence[VarBindingNode]'
    term: 'TermNode'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.LET)
        self._next()
        self.bindings = VarBindingListNode(self)
        self.term = TermNode(self)


class IdentNode(Node[Tag]):
    """
    ident = IDENT.
    """

    name: 'str'

    @Node.recover(following={Tag.BOOL, Tag.INT, Tag.LEFT_PAREN,
                             Tag.IDENT, Tag.NUMBER, Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.IDENT)
        self.name = self._image
        self._next()


class NumberNode(Node[Tag]):
    """
    number = NUMBER.
    """

    value: 'int'

    @Node.recover(following={Tag.LEFT_PAREN, Tag.IDENT, Tag.NUMBER, Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.NUMBER)
        self.value = int(self._image)
        self._next()


class SortedVarNode(Node[Tag]):
    """
    sorted-var = ident sort.
    """

    ident: 'IdentNode'
    sort: 'SortNode'

    # @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self.ident = IdentNode(self)
        self.sort = SortNode(self)


class SortedVarListNode(SequenceNode[Tag, SortedVarNode]):
    """
    sorted-var-list = LEFT_PAREN { LEFT_PAREN sorted-var RIGHT_PAREN } RIGHT_PAREN.
    """

    @Node.recover(following={Tag.BOOL, Tag.INT})
    def _parse_seq(self) -> 'None':
        if self._match(Tag.BOOL, Tag.INT):
            self._report("list of sorted variables in '(' and ')' expected")
        else:
            self._expect(Tag.LEFT_PAREN)
            self._next()
            missing_parentheses = self._match(Tag.IDENT)
            if missing_parentheses:
                self._report("list of sorted variables must begin with '('")
                self._append(SortedVarNode(self))
                self._expect(Tag.RIGHT_PAREN)
                self._next()
            while self._match(Tag.LEFT_PAREN):
                self._next()
                self._append(SortedVarNode(self))
                self._expect(Tag.RIGHT_PAREN)
                self._next()
            if missing_parentheses:
                self._report("list of sorted variables must end with ')'")
            else:
                self._expect(Tag.RIGHT_PAREN)
                self._next()


class SortNode(Node[Tag]):
    """
    sort = BOOL | INT.
    """

    value: 'Sort'

    __SORTS: 'Mapping[Tag, Sort]' = {
        Tag.BOOL: Sort.BOOL,
        Tag.INT: Sort.INT
    }

    @Node.recover(following={Tag.RIGHT_PAREN, Tag.LEFT_PAREN,
                             Tag.IDENT, Tag.NUMBER, Tag.BOOL, Tag.INT})
    def _parse(self) -> 'None':
        tag = self._expect(*SortNode.__SORTS.keys())
        self.value = SortNode.__SORTS[tag]
        self._next()


class SortListNode(SequenceNode[Tag, SortNode]):
    """
    sort-list = LEFT_PAREN { sort } RIGHT_PAREN.
    """

    @Node.recover(following={Tag.BOOL, Tag.INT})
    def _parse_seq(self) -> 'None':
        if self._match(Tag.BOOL, Tag.INT):
            self._report("sort list in '(' and ')' expected")
        else:
            self._expect(Tag.LEFT_PAREN)
            self._next()
            while self._match(Tag.BOOL, Tag.INT):
                self._append(SortNode(self))
            self._expect(Tag.RIGHT_PAREN)
            self._next()


class VarBindingNode(Node[Tag]):
    """
    var-binding = LEFT_PAREN ident term RIGHT_PAREN.
    """

    ident: 'IdentNode'
    term: 'TermNode'

    @Node.recover(following={Tag.LEFT_PAREN, Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self._expect(Tag.LEFT_PAREN)
        self._next()
        self.ident = IdentNode(self)
        self.term = TermNode(self)
        self._expect(Tag.RIGHT_PAREN)
        self._next()


class VarBindingListNode(SequenceNode[Tag, VarBindingNode]):
    """
    var-binding-list = LEFT_PAREN var-binding { var-binding } RIGHT_PAREN.
    """

    @Node.recover(following={Tag.LEFT_PAREN, Tag.IDENT, Tag.NUMBER})
    def _parse_seq(self) -> 'None':
        self._expect(Tag.LEFT_PAREN)
        self._next()
        self._append(VarBindingNode(self))
        while self._match(Tag.LEFT_PAREN):
            self._append(VarBindingNode(self))
        self._expect(Tag.RIGHT_PAREN)
        self._next()


# -----------------------------------------------------------------------------


class _ExprStack:
    def __init__(self) -> 'None':
        self.__nodes: 'List[Node[Tag]]' = []
        self.__expressions: 'List[Expr]' = []

    def push(self, node: 'Node[Tag]', expr: 'Expr'):
        self.__nodes.append(node)
        self.__expressions.append(expr)

    def take_off(self, count: 'int') -> 'Tuple[Tuple[Node[Tag], ...], Tuple[Expr, ...]]':
        ln = len(self)
        assert ln >= count
        nodes = tuple(self.__nodes[ln-count: ln])
        self.__nodes = self.__nodes[0: ln-count]
        es = tuple(self.__expressions[ln - count: ln])
        self.__expressions = self.__expressions[0: ln - count]
        return nodes, es

    def pop(self) -> 'Tuple[Node[Tag], Expr]':
        nodes, es = self.take_off(1)
        return nodes[0], es[0]

    def clear(self) -> 'None':
        self.__nodes.clear()
        self.__expressions.clear()

    def __len__(self) -> 'int':
        return len(self.__expressions)


@dataclass
class _Image:
    is_literal: 'bool'
    name: 'str'
    args: 'Tuple[_Image, ...]' = ()

    @property
    def is_one_liner(self) -> 'bool':
        return all(π.is_literal for π in self.args)

    def get_lines(self, indent: 'int') -> 'List[str]':
        stack: 'List[Tuple[_Image, int]]' = [(self, indent)]
        lines: 'List[str]' = []
        while len(stack) > 0:
            img, idt = stack.pop()
            if idt >= 0:
                if len(img.args) > 0:
                    header = "%s(%s" % ('\t' * idt, img.name)
                    if all(π.is_literal for π in img.args):
                        parts = (π.name for π in img.args)
                        lines.append(f"{header} {' '.join(parts)})")
                    else:
                        lines.append(header)
                        stack.append((img, -1))
                        stack.extend((π, idt+1) for π in reversed(img.args))
                else:
                    lines.append("%s%s" % ('\t' * idt, img.name))
            else:
                lines[-1] += ")"
        return lines


class SymbolTable:
    def __init__(self, mem: 'Memory'):
        self.__mem = mem
        self.__name_to_symbol: 'MutableMapping[str, Symbol]' = TransactionalMapping(mem)
        self.__symbol_to_name: 'MutableMapping[Symbol, str]' = TransactionalMapping(mem)
        self.__symbol_to_name.update((sym, name) for name, sym in SymbolTable.__standard_symbols.items())
        self.__symbol_to_name[BooleanEqSymbol()] = "="
        self.__symbol_to_name[IntegerEqSymbol()] = "="
        self.__symbol_to_name[NegatorSymbol(Sort.INT)] = "-"
        self.__symbol_to_name[IntegerDiffSymbol()] = "-"

    __standard_symbols: 'Mapping[str, ValencySymbol]' = {
        "true": BooleanConstSymbol(True),
        "false": BooleanConstSymbol(False),
        "not": NegatorSymbol(Sort.BOOL),
        "and": BooleanConnectiveSymbol(True),
        "or": BooleanConnectiveSymbol(False),
        "=>": BooleanImplicationSymbol(),
        "+": IntegerSumSymbol()
    }

    __standard_polymorphic_symbols: 'Set[str]' = {"=", "-"}

    def get_symbol(self, name: 'str', arg_sorts: 'Tuple[Sort, ...]') -> 'Optional[Symbol]':
        symbol = SymbolTable.__standard_symbols.get(name)
        if symbol is None:
            if name == "=":
                symbol = IntegerEqSymbol() \
                    if len(arg_sorts) > 0 and arg_sorts[0] == Sort.INT \
                    else BooleanEqSymbol()
            elif name == "-":
                symbol = NegatorSymbol(Sort.INT) \
                    if len(arg_sorts) == 1 \
                    else IntegerDiffSymbol()
            else:
                symbol = self.__name_to_symbol.get(name)
        return symbol

    def get_name(self, symbol: 'Symbol', default: 'str' = None) -> 'Optional[str]':
        return self.__symbol_to_name.get(symbol, default)

    def declare(self, name: 'str', symbol: 'Symbol') -> 'bool':
        if SymbolTable.is_standard_symbol(name) or \
                (cast(TransactionalMapping, self.__name_to_symbol).top_contains(name)):
            return False
        self.__name_to_symbol[name] = symbol
        assert symbol not in self.__symbol_to_name
        self.__symbol_to_name[symbol] = name
        return True

    def serialize_expr(self, expr: 'Expr') -> 'str':
        seen: 'MutableSet[Expr]' = set()
        labels: 'MutableMapping[Expr, str]' = {}

        def find_duplicates(e: 'Expr') -> 'None':
            for π in e.args:
                if (π in seen) and (len(π.args) > 0) and not isinstance(π.symbol, NegatorSymbol):
                    labels[π] = f"[{len(labels)+1}]"
                else:
                    seen.add(π)

        tseitin_vars: 'MutableMapping[TseitinVarSymbol, str]' = {}

        def name_of(sym: 'Symbol') -> 'str':
            name = self.get_name(sym)
            if (name is None) and (isinstance(sym, TseitinVarSymbol)):
                name = tseitin_vars.get(sym)
                if name is None:
                    tseitin_vars[sym] = name = f"τ{len(tseitin_vars)}"
            return "{?}" if name is None else name

        refs: 'List[Tuple[str, _Image]]' = []

        def make_image(e: 'Expr', values: 'Tuple[_Image, ...]') -> '_Image':
            name = name_of(e.symbol)
            if isinstance(e.symbol, NegatorSymbol) and values[0].is_literal:
                return _Image(True, f"({name} {values[0].name})")
            image = _Image(len(values) == 0, name, values)
            if e in labels:
                var = labels[e]
                refs.append((var, image))
                image = _Image(True, var)
            return image

        expr.bottom_up(find_duplicates)
        lines = expr.bottom_up_eval(make_image).get_lines(0)
        if len(refs) > 0:
            lines.append("where")
            for v, img in refs:
                lines.append(f"\t{v}:")
                lines.extend(img.get_lines(2))

        return "\n".join(lines)

    def __iter__(self) -> 'Iterator[str]':
        return iter(sorted(self.__name_to_symbol.keys()))

    @staticmethod
    def is_standard_symbol(name: 'str') -> 'bool':
        return (name in SymbolTable.__standard_symbols) or \
               (name in SymbolTable.__standard_polymorphic_symbols)


class Smtlib(VoidVisitor[Tag]):
    def __init__(self, ms: 'MessageSet') -> 'None':
        self.__ms = ms
        self.__mem = Memory()
        self.__symbols = SymbolTable(self.__mem)
        self.__assertions: 'MutableSet[Expr]' = TransactionalSet(self.__mem)
        self.__stack = _ExprStack()
        self.__model: 'Optional[Model]' = None

    @property
    def symbols(self) -> 'SymbolTable':
        return self.__symbols

    @property
    def assertion(self) -> 'Expr':
        if len(self.__assertions) == 0:
            return boolean(True)
        return boolean_and(*self.__assertions)

    def execute(self, pos: 'Position') -> 'None':
        self._visit(CommandListNode(Scanner(pos, self.__ms)))

    def _visit_command_list_node(self, node: 'CommandListNode') -> 'None':
        for command in node.seq:
            self._visit(command)

    def _visit_command_node(self, node: 'CommandNode') -> 'None':
        self._visit(node.content)

    def _visit_assert_node(self, node: 'AssertNode') -> 'None':
        self._visit(node.term)
        _, expr = self.__stack.pop()
        if expr.symbol.sort != Sort.UNKNOWN and expr.symbol.sort != Sort.BOOL:
            self.__ms.add(Message(node.term.start, "invalid assert command, term is not Bool"))
        if not expr.has_wrappers:
            self.__assertions.add(expr)

    def _visit_check_sat_node(self, _: 'CheckSatNode') -> 'None':
        self.__model = Model(self.assertion)
        self.__model.solve()
        print(self.__model.status)

    def _visit_declare_const_node(self, node: 'DeclareConstNode') -> 'None':
        sort = node.sort.value if node.sort.is_consistent else Sort.UNKNOWN
        self.__declare_symbol(node.ident, VariableSymbol(sort))

    def _visit_declare_fun_node(self, node: 'DeclareFunNode') -> 'None':
        arg_sorts = tuple(π.value if π.is_consistent else Sort.UNKNOWN for π in node.args)
        sort = node.sort.value if node.sort.is_consistent else Sort.UNKNOWN
        symbol = FunctionSymbol(sort, arg_sorts)
        self.__declare_symbol(node.ident, symbol)

    def _visit_define_fun_node(self, node: 'DefineFunNode') -> 'None':
        tr = self.__mem.begin_transaction()
        formal_args: 'List[VariableSymbol]' = []
        for π in node.args:
            var_sort = π.sort.value if π.sort.is_consistent else Sort.UNKNOWN
            var = VariableSymbol(var_sort)
            formal_args.append(var)
            self.__declare_symbol(π.ident, var)
        self._visit(node.term)
        _, body = self.__stack.pop()
        tr.rollback()

        sort = body.symbol.sort
        if node.sort.is_consistent:
            sort = node.sort.value
        if isinstance(body.symbol, ValencySymbol) and sort != body.symbol.sort:
            self.__ms.add(Message(node.sort.start, "invalid function definition, sort mismatch"))
        symbol = MacroSymbol(sort, tuple(formal_args), body)
        self.__declare_symbol(node.ident, symbol)

    def _visit_get_model_node(self, node: 'CheckSatNode') -> 'None':
        if (self.__model is None) or (self.__model.status is Status.UNSAT):
            self.__ms.add(Message(node.start, "model not available"))
        else:
            for name in self.__symbols:
                sym = self.__symbols.get_symbol(name, ())
                assert sym is not None
                if isinstance(sym, VariableSymbol):
                    expr = self.__model.eval(sym.apply())
                    if expr is not None:
                        s = self.__symbols.serialize_expr(expr)
                        print(f"{name}: {s}")

    def _visit_simplify_node(self, node: 'SimplifyNode') -> 'None':
        self._visit(node.term)
        _, expr = self.__stack.pop()
        print(self.__symbols.serialize_expr(to_cnf(expr)))

    def _visit_term_node(self, node: 'TermNode') -> 'None':
        self._visit(node.content)

    def _visit_inconsistent_term_node(self, node: 'TermNode') -> 'None':
        self.__stack.push(node, WrapperSymbol().apply())

    def _visit_call_expr_node(self, node: 'CallExprNode') -> 'None':
        for term in node.args:
            self._visit(term)
        if node.ident.is_consistent:
            self.__apply_symbol(node.ident, len(node.args))
        else:
            self.__stack.push(node, WrapperSymbol().apply())

    def _visit_inconsistent_call_expr_node(self, node: 'IdentNode') -> 'None':
        self.__stack.push(node, WrapperSymbol().apply())

    def _visit_let_expr_node(self, node: 'LetExprNode') -> 'None':
        symbols: 'List[IdentNode]' = []
        es: 'List[Expr]' = []
        for binding in node.bindings:
            if binding.is_consistent:
                self._visit(binding.term)
                _, e = self.__stack.pop()
                symbols.append(binding.ident)
                es.append(e)

        tr = self.__mem.begin_transaction()
        table: 'MutableMapping[Expr, Expr]' = {}
        for i in range(len(symbols)):
            var = VariableSymbol(es[i].symbol.sort)
            table[var.apply()] = es[i]
            self.__declare_symbol(symbols[i], var)
        self._visit(node.term)
        _, expr = self.__stack.pop()
        self.__stack.push(node, expr.substitute(table))
        tr.rollback()

    def _visit_inconsistent_let_expr_node(self, node: 'IdentNode') -> 'None':
        self.__stack.push(node, WrapperSymbol().apply())

    def _visit_ident_node(self, node: 'IdentNode') -> 'None':
        self.__apply_symbol(node, 0)

    def _visit_inconsistent_ident_node(self, node: 'IdentNode') -> 'None':
        self.__stack.push(node, WrapperSymbol().apply())

    def _visit_number_node(self, node: 'NumberNode') -> 'None':
        self.__stack.push(node, integer(node.value))

    def _visit_inconsistent_number_node(self, node: 'IdentNode') -> 'None':
        self.__stack.push(node, WrapperSymbol().apply())

    def __declare_symbol(self, node: 'IdentNode', symbol: 'Symbol') -> 'None':
        if node.is_consistent:
            name = node.name
            if not self.__symbols.declare(name, symbol):
                if SymbolTable.is_standard_symbol(name):
                    self.__ms.add(Message(node.start, f"invalid declaration, builtin symbol '{name}'"))
                else:
                    self.__ms.add(Message(node.start, f"invalid declaration, symbol '{name}' already declared"))

    def __apply_symbol(self, node: 'IdentNode', args_num: 'int') -> 'None':
        assert node.is_consistent
        nodes, es = self.__stack.take_off(args_num)
        arg_sorts = tuple(ε.symbol.sort for ε in es)
        name = node.name
        symbol = self.__symbols.get_symbol(name, arg_sorts)
        if symbol is None:
            self.__ms.add(Message(node.start, f"symbol '{name}' not declared"))
            symbol = WrapperSymbol()
            self.__symbols.declare(name, symbol)

        expr = symbol.apply(*es)
        self.__stack.push(node, expr)
        if isinstance(symbol, ValencySymbol) and isinstance(expr.symbol, WrapperSymbol):
            for i in range(args_num):
                pos = nodes[i].start
                actual_sort, formal_sort = arg_sorts[i], symbol.get_arg_sort(i, True)
                if formal_sort is None:
                    self.__ms.add(Message(pos, f"extra argument passed to function '{name}'"))
                    break
                if actual_sort != Sort.UNKNOWN and actual_sort != formal_sort:
                    self.__ms.add(Message(pos, f"sort mismatch at argument #{i+1} for function '{name}'"))
            if symbol.get_arg_sort(args_num, False) is not None:
                pos = nodes[-1].follow if args_num > 0 else node.follow
                self.__ms.add(Message(pos, f"not enough arguments ({args_num}) passed to function '{name}'"))

# -----------------------------------------------------------------------------
