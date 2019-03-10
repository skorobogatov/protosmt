from typing import List, Iterator, TypeVar, Generic
from abc import ABC, abstractmethod


# -----------------------------------------------------------------------------


_E = TypeVar('_E')


class VectorBase(Generic[_E], ABC):
    @abstractmethod
    def _get_count(self) -> 'int':
        pass

    @abstractmethod
    def _set_count(self, value: 'int') -> 'None':
        pass

    @abstractmethod
    def _get_element(self, index: 'int') -> '_E':
        pass

    @abstractmethod
    def _set_element(self, index: 'int', e: '_E') -> 'None':
        pass

    def append(self, e: '_E') -> 'None':
        count = self._get_count()
        self._set_count(count + 1)
        self._set_element(count, e)

    def truncate(self, index: 'int') -> 'None':
        self._set_count(self.__normalize_index(index))

    def remove_by_pop(self, index: 'int') -> 'None':
        i = self.__normalize_index(index)
        count = self._get_count() - 1
        self._set_count(count)
        if i < count:
            self._set_element(i, self._get_element(count))

    def __setitem__(self, index: 'int', e: '_E') -> 'None':
        self._set_element(self.__normalize_index(index), e)

    def __getitem__(self, index: 'int') -> '_E':
        return self._get_element(self.__normalize_index(index))

    def __iter__(self) -> 'Iterator[_E]':
        return (self._get_element(i) for i in range(self._get_count()))

    def __reversed__(self) -> 'Iterator[_E]':
        return (self._get_element(i) for i in reversed(range(self._get_count())))

    def __len__(self) -> 'int':
        return self._get_count()

    def __normalize_index(self, index: 'int') -> 'int':
        count = self._get_count()
        if index < 0:
            index += count
        if index < 0 or index >= count:
            raise IndexError
        return index


# -----------------------------------------------------------------------------


class Vector(Generic[_E], VectorBase[_E]):
    def __init__(self) -> 'None':
        super().__init__()
        self.__count = 0
        self.__elements: 'List[_E]' = []

    def _get_count(self) -> 'int':
        return self.__count

    def _set_count(self, value: 'int') -> 'None':
        self.__count = value

    def _get_element(self, index: 'int') -> '_E':
        return self.__elements[index]

    def _set_element(self, index: 'int', e: '_E') -> 'None':
        if index < len(self.__elements):
            self.__elements[index] = e
        else:
            self.__elements.append(e)


# -----------------------------------------------------------------------------
