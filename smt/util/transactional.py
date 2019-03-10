from typing import Any, Optional, MutableSet, MutableMapping, Iterator, TypeVar, Generic
from typing_extensions import Protocol
from abc import ABC, abstractmethod
from weakref import WeakKeyDictionary

from smt.util.unique import Unique
from smt.util.vector import VectorBase, Vector


# -----------------------------------------------------------------------------


class _Handle(Unique):
    pass


class _Chunk(ABC):
    @abstractmethod
    def update(self, chunk: '_Chunk'):
        pass


class Memory(Unique):
    transactions: 'Vector[Transaction]'

    def __init__(self) -> 'None':
        self.transactions = Vector()
        self.begin_transaction()

    def begin_transaction(self) -> 'Transaction':
        t = Transaction(self)
        self.transactions.append(t)
        return t


class Transaction(Unique):
    storage: 'MutableMapping[_Handle, _Chunk]'
    __index: 'int'
    __mem: 'Memory'

    def __init__(self, mem: 'Memory') -> 'None':
        self.storage = WeakKeyDictionary()
        self.__index = len(mem.transactions)
        self.__mem = mem

    def rollback(self) -> 'None':
        ts = self.__mem.transactions
        assert (self.__index < len(ts)) and (ts[self.__index] == self)
        ts.truncate(self.__index)

    def commit(self) -> 'None':
        ts = self.__mem.transactions
        assert (0 < self.__index < len(ts)) and (ts[self.__index] == self)
        prev = ts[self.__index - 1]
        for handle, chunk in self.storage.items():
            prev_chunk = prev.storage.get(handle)
            if prev_chunk is None:
                prev.storage[handle] = chunk
            else:
                prev_chunk.update(chunk)
        for i in range(self.__index, len(ts) - 1):
            ts[i] = t = ts[i+1]
            t.__index = i
        ts.truncate(-1)


# -----------------------------------------------------------------------------


_C = TypeVar('_C', bound=_Chunk)


class _TransactionalBase(Generic[_C], ABC):
    def __init__(self, mem: 'Memory'):
        self.__mem = mem
        self.__handle = _Handle()

    @abstractmethod
    def _create_chunk(self) -> '_C':
        pass

    @abstractmethod
    def _cast_chunk(self, chunk: '_Chunk') -> '_C':
        pass

    def _get_top_chunk(self) -> 'Optional[_C]':
        top = self.__mem.transactions[-1]
        chunk = top.storage.get(self.__handle)
        return None if chunk is None else self._cast_chunk(chunk)

    def _force_get_top_chunk(self) -> '_C':
        chunk = self._get_top_chunk()
        if chunk is None:
            chunk = self._create_chunk()
            top = self.__mem.transactions[-1]
            top.storage[self.__handle] = chunk
        return chunk

    def _get_chunks(self) -> 'Iterator[_C]':
        for t in reversed(self.__mem.transactions):
            chunk = t.storage.get(self.__handle)
            if chunk is not None:
                yield self._cast_chunk(chunk)


# -----------------------------------------------------------------------------


_V = TypeVar('_V')


class _ValueChunk(Generic[_V], _Chunk):
    value: '_V'

    def update(self, chunk: '_Chunk') -> 'None':
        assert isinstance(chunk, _ValueChunk)
        self.value = chunk.value


class Transactional(Generic[_V], _TransactionalBase[_ValueChunk[_V]]):
    def __init__(self, mem: 'Memory', v: '_V') -> 'None':
        super().__init__(mem)
        self.value = v

    def _create_chunk(self) -> '_ValueChunk[_V]':
        return _ValueChunk()

    def _cast_chunk(self, chunk: '_Chunk') -> '_ValueChunk[_V]':
        assert isinstance(chunk, _ValueChunk)
        return chunk

    @property
    def value(self) -> '_V':
        return next(self._get_chunks()).value

    @value.setter
    def value(self, v: '_V') -> 'None':
        self._force_get_top_chunk().value = v


# -----------------------------------------------------------------------------


class __IsHashable(Protocol):
    @abstractmethod
    def __hash__(self):
        pass

    @abstractmethod
    def __eq__(self, other):
        pass


_K = TypeVar('_K', bound=__IsHashable)


class _SetChunk(Generic[_K], _Chunk):
    def __init__(self) -> 'None':
        self.removed: 'MutableSet[_K]' = set()
        self.added: 'MutableSet[_K]' = set()

    def update(self, chunk: '_Chunk') -> 'None':
        assert isinstance(chunk, _SetChunk) and \
               len(self.added & chunk.added) == 0 and len(self.removed & chunk.removed) == 0
        common = self.added & chunk.removed
        self.added |= chunk.added
        self.removed |= chunk.removed
        if len(common) > 0:
            self.added -= common
            self.removed -= common


class TransactionalSet(Generic[_K], _TransactionalBase[_SetChunk[_K]], MutableSet[_K]):
    def _create_chunk(self) -> '_SetChunk[_K]':
        return _SetChunk()

    def _cast_chunk(self, chunk: '_Chunk') -> '_SetChunk[_K]':
        assert isinstance(chunk, _SetChunk)
        return chunk

    def add(self, x: '_K') -> 'None':
        if x not in self:
            chunk = self._force_get_top_chunk()
            if x in chunk.removed:
                chunk.removed.remove(x)
            else:
                chunk.added.add(x)

    def discard(self, x: '_K') -> 'None':
        if x in self:
            chunk = self._force_get_top_chunk()
            if x in chunk.added:
                chunk.added.remove(x)
            else:
                chunk.removed.add(x)

    def __contains__(self, x: 'Any') -> 'bool':
        for chunk in self._get_chunks():
            if x in chunk.added:
                return True
            if x in chunk.removed:
                break
        return False

    def __len__(self) -> 'int':
        return sum(len(chunk.added) - len(chunk.removed) for chunk in self._get_chunks())

    def __iter__(self) -> 'Iterator[_K]':
        removed: 'MutableSet[_K]' = set()
        for chunk in self._get_chunks():
            for k in chunk.added:
                if k not in removed:
                    yield k
            removed |= chunk.removed


# -----------------------------------------------------------------------------


class _MappingChunk(Generic[_K, _V], _Chunk):
    def __init__(self) -> 'None':
        self.removed: 'MutableSet[_K]' = set()
        self.unique: 'MutableMapping[_K, _V]' = {}
        self.overriding: 'MutableMapping[_K, _V]' = {}

    def update(self, chunk: '_Chunk'):
        assert isinstance(chunk, _MappingChunk)
        for k in chunk.removed:
            if k in self.unique:
                del self.unique[k]
            else:
                if k in self.overriding:
                    del self.overriding[k]
                self.removed.add(k)
        for k, v in chunk.unique.items():
            if k in self.removed:
                self.removed.discard(k)
                self.overriding[k] = v
            else:
                self.unique[k] = v
        for k, v in chunk.overriding.items():
            if k in self.unique:
                self.unique[k] = v
            else:
                self.overriding[k] = v


class TransactionalMapping(Generic[_K, _V], _TransactionalBase[_MappingChunk[_K, _V]], MutableMapping[_K, _V]):
    def _create_chunk(self) -> '_MappingChunk[_K, _V]':
        return _MappingChunk()

    def _cast_chunk(self, chunk: '_Chunk') -> '_MappingChunk[_K, _V]':
        assert isinstance(chunk, _MappingChunk)
        return chunk

    def top_contains(self, k: '_K') -> 'bool':
        chunk = self._get_top_chunk()
        return (chunk is not None) and ((k in chunk.unique) or (k in chunk.overriding))

    def __setitem__(self, k: '_K', v: '_V') -> 'None':
        chunk = self._force_get_top_chunk()
        chunk.removed.discard(k)
        if (k in self) and (k not in chunk.unique):
            chunk.overriding[k] = v
        else:
            chunk.unique[k] = v

    def __delitem__(self, k: '_K') -> 'None':
        chunk = self._force_get_top_chunk()
        if k in chunk.unique:
            del chunk.unique[k]
        elif k in self:
            if k in chunk.overriding:
                del chunk.overriding[k]
            chunk.removed.add(k)
        else:
            raise KeyError(f"Cannot find '{k}'")

    def __getitem__(self, k: '_K') -> '_V':
        for chunk in self._get_chunks():
            if k in chunk.removed:
                break
            v = chunk.unique.get(k)
            if v is None:
                v = chunk.overriding.get(k)
            if v is not None:
                return v
        raise KeyError(f"Cannot find '{k}'")

    def __len__(self) -> 'int':
        return sum(len(chunk.unique) - len(chunk.removed) for chunk in self._get_chunks())

    def __iter__(self) -> 'Iterator[_K]':
        removed: 'MutableSet[_K]' = set()
        for chunk in self._get_chunks():
            for k in chunk.unique:
                if k not in removed:
                    yield k
            removed |= chunk.removed


# -----------------------------------------------------------------------------


class TransactionalVector(Generic[_V], VectorBase[_V]):
    def __init__(self, mem: 'Memory') -> 'None':
        self.__count: 'Transactional[int]' = Transactional(mem, 0)
        self.__elements: 'TransactionalMapping[int, _V]' = TransactionalMapping(mem)

    def _get_count(self) -> 'int':
        return self.__count.value

    def _set_count(self, value: 'int') -> 'None':
        self.__count.value = value

    def _get_element(self, index: 'int') -> '_V':
        return self.__elements[index]

    def _set_element(self, index: 'int', e: '_V') -> 'None':
        self.__elements[index] = e


# -----------------------------------------------------------------------------
