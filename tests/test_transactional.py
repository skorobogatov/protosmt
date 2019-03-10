from typing import Optional
from unittest import TestCase

from smt.util import Memory, Transactional, TransactionalSet, TransactionalMapping


# -----------------------------------------------------------------------------


class TestTransactional(TestCase):
    def test_transactions_on_value(self):
        mem = Memory()
        x: 'Transactional[Optional[str]]' = Transactional(mem, None)
        self.assertIsNone(x.value)

        t1 = mem.begin_transaction()
        x.value = "a"
        self.assertEqual("a", x.value)

        t2 = mem.begin_transaction()
        self.assertEqual("a", x.value)
        x.value = "b"
        self.assertEqual("b", x.value)

        t2.commit()
        self.assertEqual("b", x.value)

        t1.rollback()
        self.assertIsNone(x.value)

    def test_basic_operations_on_set(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))

        s.add("a")
        s.add("b")
        s.add("c")
        s.add("a")
        self.assertEqual(3, len(s))
        self.assertIn("a", s)
        self.assertIn("b", s)
        self.assertIn("c", s)
        self.assertNotIn("d", s)
        self.assertEqual(["a", "b", "c"], sorted(s))

    def test_discard_on_set(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))

        s.add("a")
        s.add("b")
        s.add("c")
        self.assertEqual(3, len(s))
        self.assertIn("a", s)
        self.assertIn("b", s)
        self.assertIn("c", s)
        self.assertEqual(["a", "b", "c"], sorted(s))

        s.discard("b")
        self.assertIn("a", s)
        self.assertNotIn("b", s)
        self.assertIn("c", s)
        self.assertEqual(["a", "c"], sorted(s))

        s.discard("c")
        self.assertIn("a", s)
        self.assertNotIn("b", s)
        self.assertNotIn("c", s)
        self.assertEqual(["a"], sorted(s))

        s.discard("a")
        self.assertNotIn("a", s)
        self.assertNotIn("b", s)
        self.assertNotIn("c", s)
        self.assertEqual([], sorted(s))

    def test_operations_on_set_with_transactions(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))

        s.add("a")
        mem.begin_transaction()
        s.add("b")
        mem.begin_transaction()
        s.add("c")
        mem.begin_transaction()
        s.add("a")
        mem.begin_transaction()
        self.assertEqual(3, len(s))
        self.assertIn("a", s)
        self.assertIn("b", s)
        self.assertIn("c", s)
        self.assertNotIn("d", s)
        self.assertEqual(["a", "b", "c"], sorted(s))

    def test_discard_on_set_with_transactions(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))

        s.add("a")
        mem.begin_transaction()
        s.add("b")
        mem.begin_transaction()
        s.add("c")
        mem.begin_transaction()
        self.assertEqual(3, len(s))
        self.assertIn("a", s)
        self.assertIn("b", s)
        self.assertIn("c", s)
        self.assertEqual(["a", "b", "c"], sorted(s))

        s.discard("b")
        mem.begin_transaction()
        self.assertIn("a", s)
        self.assertNotIn("b", s)
        self.assertIn("c", s)
        self.assertEqual(["a", "c"], sorted(s))

        s.discard("c")
        mem.begin_transaction()
        self.assertIn("a", s)
        self.assertNotIn("b", s)
        self.assertNotIn("c", s)
        self.assertEqual(["a"], sorted(s))

        s.discard("a")
        mem.begin_transaction()
        self.assertNotIn("a", s)
        self.assertNotIn("b", s)
        self.assertNotIn("c", s)
        self.assertEqual([], sorted(s))

    def test_commit_on_set(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))
        s.add("a")
        t1 = mem.begin_transaction()
        s.add("b")
        t2 = mem.begin_transaction()
        s.add("c")
        t3 = mem.begin_transaction()
        s.add("a")
        t1.commit()
        t2.commit()
        t3.commit()
        self.assertEqual(3, len(s))
        self.assertIn("a", s)
        self.assertIn("b", s)
        self.assertIn("c", s)
        self.assertNotIn("d", s)
        self.assertEqual(["a", "b", "c"], sorted(s))

    def test_discard_and_commit_on_set(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))

        s.add("a")
        s.add("b")
        t1 = mem.begin_transaction()
        s.add("c")
        s.add("d")
        s.discard("c")
        s.discard("b")
        t2 = mem.begin_transaction()
        s.add("e")
        s.discard("a")
        self.assertEqual(["d", "e"], sorted(s))

        t2.commit()
        self.assertEqual(["d", "e"], sorted(s))

        t1.commit()
        self.assertEqual(["d", "e"], sorted(s))

    def test_rollback_on_set(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))
        s.add("a")
        t1 = mem.begin_transaction()
        s.add("b")
        mem.begin_transaction()
        s.add("c")
        t3 = mem.begin_transaction()
        s.add("a")

        self.assertEqual(3, len(s))
        self.assertIn("a", s)
        self.assertIn("b", s)
        self.assertIn("c", s)
        self.assertNotIn("d", s)
        self.assertEqual(["a", "b", "c"], sorted(s))

        t3.rollback()
        self.assertEqual(3, len(s))
        self.assertIn("a", s)
        self.assertIn("b", s)
        self.assertIn("c", s)
        self.assertNotIn("d", s)
        self.assertEqual(["a", "b", "c"], sorted(s))

        t1.rollback()
        self.assertEqual(1, len(s))
        self.assertIn("a", s)
        self.assertNotIn("b", s)
        self.assertNotIn("c", s)
        self.assertNotIn("d", s)
        self.assertEqual(["a"], sorted(s))

    def test_discard_and_rollback_on_set(self):
        mem = Memory()
        s: 'TransactionalSet[str]' = TransactionalSet(mem)
        self.assertEqual(0, len(s))

        s.add("a")
        s.add("b")
        s.add("c")
        self.assertEqual(["a", "b", "c"], sorted(s))

        t1 = mem.begin_transaction()
        s.add("d")
        s.discard("a")
        mem.begin_transaction()
        s.discard("b")
        self.assertEqual(["c", "d"], sorted(s))

        t1.rollback()
        self.assertEqual(["a", "b", "c"], sorted(s))

    def test_basic_operations_on_mapping(self):
        mem = Memory()
        m: 'TransactionalMapping[int, str]' = TransactionalMapping(mem)
        self.assertEqual(0, len(m))

        m[1] = "d"
        m[2] = "b"
        m[3] = "c"
        m[1] = "a"
        self.assertEqual(3, len(m))
        self.assertIn(1, m)
        self.assertIn(2, m)
        self.assertIn(3, m)
        self.assertNotIn(4, m)
        self.assertEqual("a", m[1])
        self.assertEqual("b", m[2])
        self.assertEqual("c", m[3])
        self.assertIsNone(m.get(5))
        self.assertEqual([1, 2, 3], sorted(m))

    def test_delete_on_mapping(self):
        mem = Memory()
        m: 'TransactionalMapping[int, str]' = TransactionalMapping(mem)
        self.assertEqual(0, len(m))

        m[1] = "a"
        m[2] = "b"
        m[3] = "c"
        del m[2]
        self.assertEqual(2, len(m))
        self.assertIn(1, m)
        self.assertNotIn(2, m)
        self.assertIn(3, m)
        self.assertEqual("a", m[1])
        self.assertEqual("c", m[3])
        self.assertEqual([1, 3], sorted(m))

    def test_operations_on_mapping_with_transactions(self):
        mem = Memory()
        m: 'TransactionalMapping[int, str]' = TransactionalMapping(mem)
        self.assertEqual(0, len(m))
        m[1] = "d"
        mem.begin_transaction()
        m[2] = "b"
        mem.begin_transaction()
        mem.begin_transaction()
        m[3] = "c"
        mem.begin_transaction()
        m[1] = "a"
        self.assertEqual(3, len(m))
        self.assertIn(1, m)
        self.assertIn(2, m)
        self.assertIn(3, m)
        self.assertNotIn(4, m)
        self.assertEqual("a", m[1])
        self.assertEqual("b", m[2])
        self.assertEqual("c", m[3])
        self.assertIsNone(m.get(5))
        self.assertEqual([1, 2, 3], sorted(m))

    def test_delete_on_mapping_with_transactions(self):
        mem = Memory()
        m: 'TransactionalMapping[int, str]' = TransactionalMapping(mem)
        self.assertEqual(0, len(m))

        m[1] = "a"
        mem.begin_transaction()
        m[2] = "b"
        mem.begin_transaction()
        m[3] = "c"
        mem.begin_transaction()
        del m[2]
        self.assertEqual(2, len(m))
        self.assertIn(1, m)
        self.assertNotIn(2, m)
        self.assertIn(3, m)
        self.assertEqual("a", m[1])
        self.assertEqual("c", m[3])
        self.assertEqual([1, 3], sorted(m))

        m[2] = "d"
        self.assertEqual(3, len(m))
        self.assertIn(1, m)
        self.assertIn(2, m)
        self.assertIn(3, m)
        self.assertEqual("a", m[1])
        self.assertEqual("d", m[2])
        self.assertEqual("c", m[3])
        self.assertEqual([1, 2, 3], sorted(m))

    def test_commit_on_mapping(self):
        mem = Memory()
        m: 'TransactionalMapping[str, int]' = TransactionalMapping(mem)
        m["apple"] = 10
        m["tomato"] = 20
        t1 = mem.begin_transaction()
        m["apple"] = 30
        m["potato"] = 40
        t2 = mem.begin_transaction()
        m["tomato"] = 50
        m["potato"] = 60
        self.assertEqual(3, len(m))
        self.assertEqual(30, m["apple"])
        self.assertEqual(50, m["tomato"])
        self.assertEqual(60, m["potato"])
        self.assertEqual(["apple", "potato", "tomato"], sorted(m))
        t1.commit()
        self.assertEqual(3, len(m))
        self.assertEqual(30, m["apple"])
        self.assertEqual(50, m["tomato"])
        self.assertEqual(60, m["potato"])
        self.assertEqual(["apple", "potato", "tomato"], sorted(m))
        t2.commit()
        self.assertEqual(3, len(m))
        self.assertEqual(30, m["apple"])
        self.assertEqual(50, m["tomato"])
        self.assertEqual(60, m["potato"])
        self.assertEqual(["apple", "potato", "tomato"], sorted(m))

    def test_delete_and_commit_on_mapping_v1(self):
        mem = Memory()
        m: 'TransactionalMapping[str, int]' = TransactionalMapping(mem)

        m["a"] = 10
        m["b"] = 2
        m["c"] = 30
        t1 = mem.begin_transaction()
        m["b"] *= 10
        m["d"] = 40
        del m["a"]
        self.assertEqual(3, len(m))
        self.assertEqual(20, m["b"])
        self.assertEqual(30, m["c"])
        self.assertEqual(40, m["d"])
        self.assertEqual(["b", "c", "d"], sorted(m))

        t1.commit()
        self.assertEqual(3, len(m))
        self.assertEqual(20, m["b"])
        self.assertEqual(30, m["c"])
        self.assertEqual(40, m["d"])
        self.assertEqual(["b", "c", "d"], sorted(m))

    def test_delete_and_commit_on_mapping_v2(self):
        mem = Memory()
        m: 'TransactionalMapping[str, int]' = TransactionalMapping(mem)

        m["a"] = 1
        mem.begin_transaction()
        m["b"] = 20
        del m["a"]
        t1 = mem.begin_transaction()
        m["a"] = 10
        self.assertEqual(2, len(m))
        self.assertEqual(10, m["a"])
        self.assertEqual(20, m["b"])
        self.assertEqual(["a", "b"], sorted(m))

        t1.commit()
        self.assertEqual(2, len(m))
        self.assertEqual(10, m["a"])
        self.assertEqual(20, m["b"])
        self.assertEqual(["a", "b"], sorted(m))

    def test_rollback_on_mapping(self):
        mem = Memory()
        m: 'TransactionalMapping[str, int]' = TransactionalMapping(mem)
        m["apple"] = 10
        m["tomato"] = 20
        t1 = mem.begin_transaction()
        m["apple"] = 30
        m["potato"] = 40
        t2 = mem.begin_transaction()
        m["tomato"] = 50
        m["potato"] = 60
        self.assertEqual(3, len(m))
        self.assertEqual(30, m["apple"])
        self.assertEqual(50, m["tomato"])
        self.assertEqual(60, m["potato"])
        self.assertEqual(["apple", "potato", "tomato"], sorted(m))
        t2.rollback()
        self.assertEqual(3, len(m))
        self.assertEqual(30, m["apple"])
        self.assertEqual(20, m["tomato"])
        self.assertEqual(40, m["potato"])
        self.assertEqual(["apple", "potato", "tomato"], sorted(m))
        t1.rollback()
        self.assertEqual(2, len(m))
        self.assertEqual(10, m["apple"])
        self.assertEqual(20, m["tomato"])
        self.assertEqual(["apple", "tomato"], sorted(m))

    def test_delete_and_rollback_on_mapping(self):
        mem = Memory()
        m: 'TransactionalMapping[str, int]' = TransactionalMapping(mem)

        m["a"] = 1
        m["b"] = 20
        mem.begin_transaction()
        m["c"] = 30
        del m["a"]
        t1 = mem.begin_transaction()
        m["a"] = 10
        self.assertEqual(3, len(m))
        self.assertEqual(10, m["a"])
        self.assertEqual(20, m["b"])
        self.assertEqual(30, m["c"])
        self.assertEqual(["a", "b", "c"], sorted(m))

        t1.rollback()
        self.assertEqual(2, len(m))
        self.assertEqual(20, m["b"])
        self.assertEqual(30, m["c"])
        self.assertEqual(["b", "c"], sorted(m))


# -----------------------------------------------------------------------------
