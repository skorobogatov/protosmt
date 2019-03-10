from typing import Optional, List, Tuple
from unittest import TestCase
from textwrap import dedent
import random

from smt.logic import to_cnf
from smt.interpreters import Position, MessageSet
from smt.interpreters.smtlib import Tag, Scanner, Smtlib


class TestScanner(TestCase):
    SAMPLES: 'List[Tuple[str, Tag]]' = [
        ("(", Tag.LEFT_PAREN),
        (")", Tag.RIGHT_PAREN),
        ("+", Tag.IDENT),
        ("x", Tag.IDENT),
        ("x1", Tag.IDENT),
        ("x-files", Tag.IDENT),
        ("Bool", Tag.BOOL),
        ("assert", Tag.ASSERT),
        ("check-sat", Tag.CHECK_SAT),
        ("declare-const", Tag.DECLARE_CONST),
        ("declare-fun", Tag.DECLARE_FUN),
        ("define-fun", Tag.DEFINE_FUN),
        ("let", Tag.LET),
    ]

    def assertToken(self, scanner: 'Scanner', start: 'Position', follow: 'Position', tag: 'Optional[Tag]'):
        self.assertEqual(start, scanner.start)
        self.assertEqual(follow, scanner.follow)
        self.assertEqual(tag, scanner.tag)

    def test_tags(self):
        for (text, tag) in TestScanner.SAMPLES:
            with self.subTest(text=text):
                start = Position.beginning_of("dummy.txt", text)
                follow = start.skip(len(text))

                ms = MessageSet()
                scanner = Scanner(start, ms)
                self.assertEqual(0, len(ms))
                self.assertToken(scanner, start, follow, tag)

    def test_empty_sequences(self):
        for text in TestScanner.DELIMITERS:
            pos = Position.beginning_of("dummy.txt", text).skip(len(text))
            seq = (text, [(pos, pos, None)])
            self.check_sequence(seq)

    def test_all_pairs(self):
        random.seed(200)
        self.check_all_sequences(2)

    def tst_some_long_sequences(self):
        random.seed(300)
        for size in range(3, 100):
            n = 100 if size <= 10 else 1
            self.check_some_sequences(size, n)

    Sequence = Tuple[str, List[Tuple[Position, Position, Optional[Tag]]]]

    def check_all_sequences(self, size: 'int'):
        ln = len(TestScanner.SAMPLES)
        for task in range(0, ln ** size):
            indexes: 'List[int]' = []
            for i in range(0, size):
                indexes.append(task % ln)
                task //= ln
            seq = TestScanner.get_sequence(indexes)
            self.check_sequence(seq)

    def check_some_sequences(self, size: 'int', n: 'int'):
        for t in range(0, n):
            indexes: 'List[int]' = []
            for i in range(0, size):
                indexes.append(random.randint(0, len(TestScanner.SAMPLES) - 1))
            seq = TestScanner.get_sequence(indexes)
            self.check_sequence(seq)

    def check_sequence(self, seq: 'Sequence'):
        (text, tokens) = seq
        # print(repr(text))
        with self.subTest(text=text):
            pos = Position.beginning_of("dummy.txt", text)
            ms = MessageSet()
            scanner = Scanner(pos, ms)
            for i in range(0, len(tokens)):
                (start, follow, tag) = tokens[i]
                self.assertEqual(0, len(ms))
                self.assertToken(scanner, start, follow, tag)
                scanner.read_token()

    @staticmethod
    def get_sequence(indexes: 'List[int]') -> 'Sequence':
        samples: 'List[Tuple[str, Tag]]' = []
        for i in indexes:
            samples.append(TestScanner.SAMPLES[i])

        images: 'List[str]' = []
        delimiters: 'List[str]' = []
        for (text, tag) in samples:
            delimiter = TestScanner.get_random_delimiter(tag != Tag.LEFT_PAREN and tag != Tag.RIGHT_PAREN)
            delimiters.append(delimiter)
            images.append(text + delimiter)

        s = "".join(images)
        pos = Position.beginning_of("dummy.txt", s)

        tokens: 'List[Tuple[Position, Position, Optional[Tag]]]' = []
        for i in range(0, len(indexes)):
            (text, tag) = samples[i]
            start = pos
            pos = pos.skip(len(text))
            tokens.append((start, pos, tag))
            pos = pos.skip(len(delimiters[i]))
        tokens.append((pos, pos, None))

        return s, tokens

    DELIMITERS = [
        "", " ", "\t ", " \t", "\n", " \n", "\n ", "   ", "\n\n\n",
        "; this is comment\n", ";;;;;;;;\n", "  ; \t\n"
    ]

    @staticmethod
    def get_random_delimiter(non_empty: 'bool') -> 'str':
        delimiters = TestScanner.DELIMITERS
        while True:
            delimiter = delimiters[random.randint(0, len(delimiters) - 1)]
            if len(delimiter) > 0 or not non_empty:
                return delimiter


class TestInterpreter(TestCase):
    def check(self, src: 'str', expected: 'str'):
        ms = MessageSet()
        interpreter = Smtlib(ms)
        pos = Position.beginning_of("test.smt", src)
        interpreter.execute(pos)
        self.assertEqual(0, len(ms))
        a = interpreter.symbols.serialize_expr(to_cnf(interpreter.assertion))
        self.assertEqual(dedent(expected.replace("\t", "    ")), a.replace("\t", "    "))

    def test_1(self):
        src = """
        (declare-const A Bool)
        (declare-const B Bool)
        (assert A)
        (assert B)
        """
        expected = "(and A B)"
        self.check(src, expected)

    def test_2(self):
        src = """
        (declare-const A Int)
        (declare-const B Int)
        (assert (= A B))
        """
        expected = "(= A B)"
        self.check(src, expected)

    def test_3(self):
        src = """
        (declare-const A Bool)
        (declare-const B Bool)
        (define-fun F ((x Bool) (y Bool)) Bool
            (and x y))
        (assert (F A B))
        """
        expected = "(and A B)"
        self.check(src, expected)

    def test_4(self):
        src = """
        (declare-const A Bool)
        (declare-const B Bool)
        (declare-const C Bool)
        (declare-const D Bool)
        (assert (or (and A B) (and C D)))
        """
        expected = """\
        (and
            (or (not τ0) A)
            (or (not τ0) B)
            (or (not τ1) C)
            (or (not τ1) D)
            (or (not A) (not B) τ0)
            (or (not C) (not D) τ1)
            (or τ0 τ1))"""
        self.check(src, expected)

    def test_5(self):
        src = """
        (declare-const A Bool)
        (declare-const B Bool)
        (declare-const C Bool)
        (declare-const D Bool)
        (declare-fun F (Bool Bool) Bool)
        (assert (F (and A B) (and C D)))
        """
        expected = """\
        (and
            (F τ0 τ1)
            (or (not τ0) A)
            (or (not τ0) B)
            (or (not τ1) C)
            (or (not τ1) D)
            (or (not A) (not B) τ0)
            (or (not C) (not D) τ1))"""
        self.check(src, expected)

    def test_6(self):
        src = """
        (declare-const A Bool)
        (declare-const B Bool)
        (declare-fun F (Bool) Bool)
        (assert (and (F (and A B)) (F (F (and A B)))))
        """
        expected = """\
        (and
            [1]
            (F [1])
            (or (not τ0) A)
            (or (not τ0) B)
            (or (not A) (not B) τ0))
        where
            [1]:
                (F τ0)"""
        self.check(src, expected)
