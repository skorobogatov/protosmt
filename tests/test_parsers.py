from typing import Union, Optional, Tuple, List, Mapping
from unittest import TestCase
from enum import Enum, auto

from smt.interpreters import Position, Message, MessageSet
from smt.interpreters.scanner_base import AbstractScanner
from smt.interpreters.parser_base import Node, Visitor


# -----------------------------------------------------------------------------


class TestCoords(TestCase):
    def assertPos(self, pos: 'Position', offs: 'int', line: 'int', col: 'int', ch: 'str'):
        self.assertEqual(line, pos.line)
        self.assertEqual(offs, pos.offs)
        self.assertEqual(col, pos.col)
        self.assertEqual(ch, pos.ch)

    def test_linecol_evaluation(self):
        text = "abcd\nefg\nh"
        pos = Position.beginning_of("dummy.txt", text)

        for i in range(0, 5):
            self.assertPos(pos, i, 1, i + 1, text[i])
            pos = pos.next

        for i in range(0, 4):
            self.assertPos(pos, i + 5, 2, i + 1, text[i + 5])
            pos = pos.next

        self.assertPos(pos, 9, 3, 1, "h")

        pos = pos.next
        self.assertPos(pos, 10, 3, 2, Position.EOF)
        self.assertPos(pos.next, 10, 3, 2, Position.EOF)

    def test_position_comparison(self):
        text = "abcd\nefg\nh"
        a = Position.beginning_of("dummy.txt", text)
        b = a.skip(5)
        c = b.next
        d = b.next

        self.assertTrue(a < b)
        self.assertFalse(a >= b)
        self.assertTrue(a <= b)
        self.assertFalse(a > b)
        self.assertTrue(b > a)
        self.assertFalse(b <= a)
        self.assertTrue(b >= a)
        self.assertFalse(b < a)

        self.assertTrue(c == d)
        self.assertFalse(c != d)
        self.assertTrue(b != c)
        self.assertFalse(b == c)

    def test_file_reading(self):
        import tempfile
        test_dir = tempfile.mkdtemp()

        try:
            import os
            filename = os.path.join(test_dir, "test.txt")

            f = open(filename, "w")
            f.write("abcd\nefg\nh")
            f.close()

            pos = Position.beginning_of(filename)
            self.assertPos(pos, 0, 1, 1, "a")
            self.assertPos(pos.next, 1, 1, 2, "b")
        finally:
            import shutil
            shutil.rmtree(test_dir)

    def test_position_image(self):
        text = "abcd\nefg\nh"
        a = Position.beginning_of("dummy.txt", text)
        b = a.skip(5)
        c = b.skip(4)
        self.assertEqual("efg\n", b.get_image(c))


class TestMessages(TestCase):
    def test_message_comparison_in_one_file(self):
        text = "abcd\nefg\nh"
        a = Position.beginning_of("dummy.txt", text)
        b = a.skip(5)
        c = b.next
        d = b.next
        e = b.next

        ma = Message(a, "a")
        mb = Message(b, "b")
        mc = Message(c, "x")
        md = Message(d, "x")
        me = Message(e, "y")

        self.assertTrue(ma < mb)
        self.assertFalse(ma >= mb)
        self.assertTrue(ma <= mb)
        self.assertFalse(ma > mb)
        self.assertTrue(mb > ma)
        self.assertFalse(mb <= ma)
        self.assertTrue(mb >= ma)
        self.assertFalse(mb < ma)
        self.assertTrue(mc < me)
        self.assertFalse(mc >= me)
        self.assertTrue(mc <= me)
        self.assertFalse(mc > me)

        self.assertTrue(mc == md)
        self.assertFalse(mc != md)
        self.assertTrue(mb != mc)
        self.assertFalse(mb == mc)
        self.assertFalse(mc == me)
        self.assertTrue(mc != me)

    def test_message_comparison_in_two_files(self):
        a = Position.beginning_of("a.txt", "xyz")
        b = Position.beginning_of("b.txt", "xyz")

        ma = Message(a, "M")
        mb = Message(b, "M")

        self.assertFalse(ma == mb)
        self.assertTrue(ma != mb)
        self.assertTrue(ma < mb)
        self.assertFalse(ma >= mb)
        self.assertTrue(ma <= mb)
        self.assertFalse(mb > mb)

    def assertMessageList(self, ms: 'MessageSet', expected: 'List[Tuple[Position, str]]'):
        i = 0
        for m in ms:
            (pos, text) = expected[i]
            self.assertEqual(pos, m.pos)
            self.assertEqual(text, m.description)
            i += 1

    def test_message_list_sorting(self):
        a = Position.beginning_of("file1.txt", "xyz")
        b = a.next
        c = Position.beginning_of("file2.txt", "abcd")
        d = c.next

        ms = MessageSet()
        ms.add(Message(c, "C"))
        ms.add(Message(b, "B"))
        ms.add(Message(a, "A"))
        ms.add(Message(d, "D"))

        expected = [(a, "A"), (b, "B"), (c, "C"), (d, "D")]
        self.assertMessageList(ms, expected)

    def test_message_list_uniqueness(self):
        a = Position.beginning_of("file1.txt", "xyz")
        b = a.next

        ms = MessageSet()
        ms.add(Message(b, "Z"))
        ms.add(Message(b, "Y"))
        ms.add(Message(a, "X"))
        ms.add(Message(a, "X"))

        expected = [(a, "X"), (b, "Y"), (b, "Z")]
        self.assertMessageList(ms, expected)


# -----------------------------------------------------------------------------


class Tag(Enum):
    IDENT = auto()
    NUMBER = auto()
    PLUS = auto()
    MINUS = auto()
    STAR = auto()
    SLASH = auto()
    LEFT_PAREN = auto()
    RIGHT_PAREN = auto()


class Scanner(AbstractScanner[Tag]):
    __SIGNS: 'Mapping[str, Tag]' = {
        '+': Tag.PLUS,
        '-': Tag.MINUS,
        '*': Tag.STAR,
        '/': Tag.SLASH,
        '(': Tag.LEFT_PAREN,
        ')': Tag.RIGHT_PAREN
    }

    def _scan(self) -> 'Optional[Tag]':
        while True:
            self._consume_while(str.isspace)
            self._mark_start()
            if self._consume(str.isalpha):
                self._consume_while(str.isalnum)
                return Tag.IDENT
            if self._consume(str.isdecimal):
                self._consume_while(str.isdecimal)
                return Tag.NUMBER
            if self._consume("+-*/()"):
                return Scanner.__SIGNS[self.image]
            if self._consume(Position.EOF):
                return None
            self._consume_invalid_char()


class Var(Node[Tag]):
    """
    var = IDENT.
    """

    name: 'str'

    def _parse(self) -> 'None':
        self._expect(Tag.IDENT)
        self.name = self._image
        self._next()


class Number(Node[Tag]):
    """
    number = NUMBER.
    """

    value: 'int'

    def _parse(self) -> 'None':
        self._expect(Tag.NUMBER)
        self.value = int(self._image)
        self._next()


class Negation(Node[Tag]):
    """
    negation = MINUS factor.
    """

    factor: 'Factor'

    @Node.recover(following={Tag.RIGHT_PAREN, Tag.PLUS, Tag.MINUS, Tag.STAR, Tag.SLASH})
    def _parse(self) -> 'None':
        self._expect(Tag.MINUS)
        self._next()
        self.factor = Factor(self)


class ParenthesizedExpr(Node[Tag]):
    """
    paren-expr = LEFT_PAREN expr RIGHT_PAREN.
    """

    expr: 'Expr'

    @Node.recover(ending={Tag.RIGHT_PAREN}, following={Tag.PLUS, Tag.MINUS, Tag.STAR, Tag.SLASH})
    def _parse(self) -> 'None':
        self._expect(Tag.LEFT_PAREN)
        self._next()
        self.expr = Expr(self)
        self._expect(Tag.RIGHT_PAREN)
        self._next()


class Factor(Node[Tag]):
    """
    factor = var | number | negation | LEFT_PAREN expr RIGHT_PAREN.
    """

    content: 'Union[Var, Number, Negation, ParenthesizedExpr]'

    @Node.recover(following={Tag.RIGHT_PAREN, Tag.PLUS, Tag.MINUS, Tag.STAR, Tag.SLASH})
    def _parse(self) -> 'None':
        tag = self._expect(Tag.IDENT, Tag.NUMBER, Tag.MINUS, Tag.LEFT_PAREN)
        if tag == Tag.IDENT:
            self.content = Var(self)
        elif tag == Tag.NUMBER:
            self.content = Number(self)
        elif tag == Tag.MINUS:
            self.content = Negation(self)
        else:
            self.content = ParenthesizedExpr(self)


class OpFactor(Node[Tag]):
    """
    op-factor = (STAR | SLASH) factor.
    """

    op: 'Tag'
    factor: 'Factor'

    @Node.recover(following={Tag.RIGHT_PAREN, Tag.PLUS, Tag.MINUS, Tag.STAR, Tag.SLASH})
    def _parse(self) -> 'None':
        self.op = self._expect(Tag.STAR, Tag.SLASH)
        self._next()
        self.factor = Factor(self)


class Term(Node[Tag]):
    """
    term = factor { op-factor }.
    """

    head: 'Factor'
    tail: 'Tuple[OpFactor, ...]'

    @Node.recover(following={Tag.RIGHT_PAREN, Tag.PLUS, Tag.MINUS})
    def _parse(self) -> 'None':
        self.head = Factor(self)
        tail: 'List[OpFactor]' = []
        while self._match(Tag.STAR, Tag.SLASH):
            tail.append(OpFactor(self))
        self.tail = tuple(tail)


class OpTerm(Node[Tag]):
    """
    op-term = (PLUS | MINUS) term.
    """

    op: 'Tag'
    term: 'Term'

    @Node.recover(following={Tag.RIGHT_PAREN, Tag.PLUS, Tag.MINUS})
    def _parse(self) -> 'None':
        self.op = self._expect(Tag.PLUS, Tag.MINUS)
        self._next()
        self.term = Term(self)


class Expr(Node[Tag]):
    """
    expr = term { op-term }.
    """

    head: 'Term'
    tail: 'Tuple[OpTerm, ...]'

    @Node.recover(following={Tag.RIGHT_PAREN})
    def _parse(self) -> 'None':
        self.head = Term(self)
        tail: 'List[OpTerm]' = []
        while self._match(Tag.PLUS, Tag.MINUS):
            tail.append(OpTerm(self))
        self.tail = tuple(tail)


class Printer(Visitor):
    def p(self, node: 'Node[Tag]') -> 'str':
        return self._visit(node)

    __OPS: 'Mapping[Tag, str]' = {
        Tag.STAR: "*",
        Tag.SLASH: "/",
        Tag.PLUS: "+",
        Tag.MINUS: "-"
    }

    # noinspection PyMethodMayBeStatic
    def _visit_var(self, node: 'Var') -> 'str':
        assert node.is_consistent
        return node.name

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_var(self, node: 'Var') -> 'str':
        assert not node.is_consistent
        return "<var>"

    # noinspection PyMethodMayBeStatic
    def _visit_number(self, node: 'Number') -> 'str':
        assert node.is_consistent
        return str(node.value)

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_number(self, node: 'Number') -> 'str':
        assert not node.is_consistent
        return "<number>"

    def _visit_negation(self, node: 'Negation') -> 'str':
        assert node.is_consistent
        return "-%s" % self.p(node.factor)

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_negation(self, node: 'Negation') -> 'str':
        assert not node.is_consistent
        return "-<factor>"

    def _visit_parenthesized_expr(self, node: 'ParenthesizedExpr') -> 'str':
        assert node.is_consistent
        return "(%s)" % self.p(node.expr)

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_parenthesized_expr(self, node: 'ParenthesizedExpr') -> 'str':
        assert not node.is_consistent
        return "(<expr>)"

    def _visit_factor(self, node: 'Factor') -> 'str':
        assert node.is_consistent
        return self.p(node.content)

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_factor(self, node: 'Factor') -> 'str':
        assert not node.is_consistent
        return "<factor>"

    def _visit_op_factor(self, node: 'OpFactor') -> 'str':
        assert node.is_consistent
        op = Printer.__OPS[node.op]
        return "%s%s" % (op, self.p(node.factor))

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_op_factor(self, node: 'OpFactor') -> 'str':
        assert not node.is_consistent
        return "<op_factor>"

    def _visit_term(self, node: 'Term') -> 'str':
        assert node.is_consistent
        head = self.p(node.head)
        return "%s%s" % (head, "".join(map(self.p, node.tail)))

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_term(self, node: 'Term') -> 'str':
        assert not node.is_consistent
        return "<term>"

    def _visit_op_term(self, node: 'OpTerm') -> 'str':
        assert node.is_consistent
        op = Printer.__OPS[node.op]
        return "%s%s" % (op, self.p(node.term))

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_op_term(self, node: 'OpTerm') -> 'str':
        assert not node.is_consistent
        return "<op_term>"

    def _visit_expr(self, node: 'Expr') -> 'str':
        assert node.is_consistent
        head = self.p(node.head)
        return "%s%s" % (head, "".join(map(self.p, node.tail)))

    # noinspection PyMethodMayBeStatic
    def _visit_inconsistent_expr(self, node: 'Expr') -> 'str':
        assert not node.is_consistent
        return "<expr>"


class TestArithParser(TestCase):
    def setUp(self):
        self.printer = Printer()
        pass

    def create_scanner(self, text: 'str') -> 'Scanner':
        self.ms = MessageSet()
        pos = Position.beginning_of("dummy.txt", text)
        return Scanner(pos, self.ms)

    def assertNoMessages(self):
        for msg in self.ms:
            print(msg)
        self.assertEqual(0, len(self.ms))

    def assertCoords(self, node: 'Node[Tag]', line1: 'int', col1: 'int', line2: 'int', col2: 'int'):
        self.assertEqual(line1, node.start.line)
        self.assertEqual(col1, node.start.col)
        self.assertEqual(line2, node.follow.line)
        self.assertEqual(col2, node.follow.col)

    def assertPrintout(self, expected: 'str', node: 'Node[Tag]'):
        self.assertEqual(expected, self.printer.p(node))
        pass

    def test_var(self):
        scanner = self.create_scanner("Abc")
        var = Var(scanner)
        self.assertNoMessages()
        self.assertEqual("Abc", var.name)
        self.assertCoords(var, 1, 1, 1, 4)

    def test_number(self):
        scanner = self.create_scanner("1000")
        number = Number(scanner)
        self.assertNoMessages()
        self.assertEqual(1000, number.value)
        self.assertCoords(number, 1, 1, 1, 5)

    def test_factor(self):
        scanner = self.create_scanner("Alpha")
        factor = Factor(scanner)
        self.assertNoMessages()
        self.assertIsInstance(factor.content, Var)
        self.assertCoords(factor, 1, 1, 1, 6)

    def test_op_factor(self):
        scanner = self.create_scanner("*5")
        op_factor = OpFactor(scanner)
        self.assertNoMessages()
        self.assertEqual(Tag.STAR, op_factor.op)
        self.assertCoords(op_factor, 1, 1, 1, 3)
        self.assertIsInstance(op_factor.factor.content, Number)
        self.assertCoords(op_factor.factor, 1, 2, 1, 3)

    def test_term(self):
        scanner = self.create_scanner("x*5/6")
        term = Term(scanner)
        self.assertNoMessages()
        self.assertEqual(2, len(term.tail))
        self.assertCoords(term, 1, 1, 1, 6)
        self.assertCoords(term.head, 1, 1, 1, 2)
        self.assertCoords(term.tail[0], 1, 2, 1, 4)
        self.assertCoords(term.tail[1], 1, 4, 1, 6)

    def test_op_term(self):
        scanner = self.create_scanner("+x")
        op_term = OpTerm(scanner)
        self.assertNoMessages()
        self.assertEqual(Tag.PLUS, op_term.op)
        self.assertCoords(op_term, 1, 1, 1, 3)
        self.assertCoords(op_term.term, 1, 2, 1, 3)

    def test_expr(self):
        scanner = self.create_scanner("2 + -3*(x+1)")
        expr = Expr(scanner)
        self.assertNoMessages()
        self.assertPrintout("2+-3*(x+1)", expr)

    def test_err_1(self):
        scanner = self.create_scanner("-+")
        expr = Expr(scanner)
        self.assertPrintout("-<factor>+<factor>", expr)

    def test_err_2(self):
        scanner = self.create_scanner("(2+3")
        expr = Expr(scanner)
        self.assertPrintout("(2+3)", expr)

    def test_err_3(self):
        scanner = self.create_scanner("3*(4+x/5 a)*8")
        expr = Expr(scanner)
        self.assertPrintout("3*(4+x/5)*8", expr)

# -----------------------------------------------------------------------------
