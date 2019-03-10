from typing import Any, Optional, Tuple, MutableMapping, Callable
from abc import ABC, ABCMeta
from functools import total_ordering
from weakref import WeakValueDictionary


# -----------------------------------------------------------------------------


class UniqueMeta(ABCMeta):
    def __init__(cls, name, bases, namespace) -> 'None':
        super().__init__(name, bases, namespace)
        cls._cache: 'Optional[MutableMapping[Tuple[Any, ...], Any]]' = None
        cls._transform: 'Optional[Callable]' = None

    def __call__(cls, *args, **kwargs):
        obj: 'Optional[Unique]' = None
        if cls._cache is not None:
            obj = cls._cache.get(_make_key(cls._transform, *args, **kwargs))
        if obj is None:
            obj = super().__call__(*args, **kwargs)
        return obj


@total_ordering
class Unique(ABC, metaclass=UniqueMeta):
    __key: 'Tuple[Any, ...]'
    __precomputed_hash: 'int'

    __priority: 'int' = 1000
    __count: 'int' = 0

    def __new__(cls, *args, **kwargs):
        obj = super().__new__(cls)
        key = _make_key(cls._transform, *args, **kwargs)
        obj.__key = (cls.__priority, cls.__name__, key, cls.__count)
        cls.__count += 1
        obj.__precomputed_hash = hash(obj.__key)
        if cls._cache is not None:
            cls._cache[key] = obj
        return obj

    def __eq__(self, other) -> 'bool':
        return self is other

    def __lt__(self, other) -> 'bool':
        assert isinstance(other, Unique)
        return self.__key < other.__key

    def __hash__(self) -> 'int':
        return self.__precomputed_hash

    @staticmethod
    def cached(cls):
        cls._cache = WeakValueDictionary()
        return cls

    @staticmethod
    def transform_args(transform: 'Callable'):
        def set_transform(cls):
            cls._transform = transform
            return cls
        return set_transform

    @staticmethod
    def priority(level: 'int'):
        def set_priority(cls):
            cls.__priority = level
            return cls
        return set_priority


def _make_key(transform: 'Optional[Callable]', *args, **kwargs) -> 'Tuple[Any, ...]':
    transformed_args = args if transform is None else transform(*args)
    return transformed_args, tuple(sorted(kwargs.items()))


# -----------------------------------------------------------------------------
