from typing import Union, Optional, Tuple, List, Set, MutableMapping, \
    TypeVar, Generic, Callable, NoReturn
from abc import ABC, abstractmethod
from dataclasses import dataclass
from collections.abc import Sequence

from smt.interpreters.scanner_base import Position, Message, AbstractScanner


# -----------------------------------------------------------------------------


@dataclass
class _Trampoline:
    pos: 'Position'


class _Frontier:
    def __init__(self, trampoline: '_Trampoline'):
        self.__trampoline, self.__shared = trampoline, False

    @property
    def pos(self) -> 'Position':
        return self.__trampoline.pos

    @pos.setter
    def pos(self, value: 'Position') -> 'None':
        if self.__shared:
            self.__trampoline, self.__shared = _Trampoline(value), False
        else:
            self.__trampoline.pos = value

    def share(self) -> '_Frontier':
        if self.__shared:
            self.__trampoline = _Trampoline(self.pos)
        else:
            self.__shared = True
        return _Frontier(self.__trampoline)


TAG = TypeVar('TAG')
N = TypeVar('N', bound='Node')


class Node(Generic[TAG], ABC):
    __scanner: 'AbstractScanner[TAG]'
    __frontier: '_Frontier'
    __start: 'Position'

    def __init__(self, parent: 'Union[AbstractScanner[TAG], Node[TAG]]'):
        if isinstance(parent, AbstractScanner):
            self.__scanner = parent
            self.__frontier = _Frontier(_Trampoline(self.__scanner.start))
        else:
            self.__scanner = parent.__scanner
            self.__frontier = parent.__frontier.share()

        self.__start = self.__scanner.start
        if isinstance(parent, AbstractScanner):
            try:
                self._parse()
            except Message:
                pass
        else:
            self._parse()
        self.__is_consistent = all(hasattr(self, a) for a in self.__get_annotated_attrs())

    @abstractmethod
    def _parse(self) -> 'None':
        pass

    @property
    def start(self) -> 'Position':
        return self.__start

    @property
    def follow(self) -> 'Position':
        pos = self.__frontier.pos
        return pos if self.start <= pos else self.start

    @property
    def is_consistent(self) -> 'bool':
        return self.__is_consistent

    @property
    def types(self) -> 'Tuple[type, ...]':
        return Node.__get_type_sequence(self.__class__)

    @property
    def _image(self) -> 'str':
        return self.__scanner.image

    def _next(self) -> 'Optional[TAG]':
        self.__frontier.pos = self.__scanner.follow
        self.__scanner.read_token()
        return self.__scanner.tag

    def _match(self, *tags: 'TAG') -> 'Optional[TAG]':
        assert len(tags) > 0
        if any(self.__scanner.tag == tag for tag in tags):
            return self.__scanner.tag
        return None

    def _expect(self, *tags: 'TAG') -> 'TAG':
        tag_opt = self._match(*tags)
        if tag_opt is not None:
            return tag_opt
        tag_list = ", ".join(sorted(map(str, tags)))
        description = ("%s expected" if len(tags) == 1 else "any of %s expected") % tag_list
        self._report_raise(description)

    def _report(self, description: 'str', at_start: 'bool' = True) -> 'Message':
        return self.__scanner.report(description, at_start)

    def _report_raise(self, description: 'str', at_start: 'bool' = True) -> NoReturn:
        raise self._report(description, at_start)

    @staticmethod
    def recover(ending: 'Optional[Set[TAG]]' = None, following: 'Optional[Set[TAG]]' = None):
        def decorator(node_parse: 'Callable[[Node[TAG]], None]'):
            def parse_wrapper(self: 'Node[TAG]') -> 'None':
                try:
                    node_parse(self)
                except Message:
                    sync_set: 'Set[TAG]' = set()
                    if ending is not None:
                        sync_set.update(ending)
                    if following is not None:
                        sync_set.update(following)
                    if len(sync_set) > 0:
                        sync = tuple(sync_set)
                        while not (self.__scanner.tag is None or self._match(*sync)):
                            self.__scanner.read_token()
                        if ending is not None and self._match(*ending):
                            self._next()
            return parse_wrapper
        return decorator

    __annotated_attrs: 'MutableMapping[type, List[str]]' = {}

    def __get_annotated_attrs(self) -> 'List[str]':
        attrs_list = Node.__annotated_attrs.get(self.__class__)
        if attrs_list is None:
            attrs: 'Set[str]' = set()
            for τ in self.types:
                if hasattr(τ, "__annotations__"):
                    for σ in τ.__annotations__:
                        if not σ.startswith("_"):
                            attrs.add(σ)
            Node.__annotated_attrs[self.__class__] = attrs_list = list(attrs)
        return attrs_list

    __type_sequences: 'MutableMapping[type, Tuple[type, ...]]' = {}
    __prohibited_classes: 'Set[Union[type, object]]' = {object, ABC, Generic}

    @staticmethod
    def __get_type_sequence(cls: 'type') -> 'Tuple[type, ...]':
        types: 'Optional[Tuple[type, ...]]' = Node.__type_sequences.get(cls)
        if types is None:
            classes: 'Set[type]' = set()
            seq: 'List[type]' = []
            for β in cls.__bases__:
                for κ in Node.__get_type_sequence(β):
                    if κ not in classes:
                        classes.add(κ)
                        seq.append(κ)
            if cls not in Node.__prohibited_classes:
                seq.append(cls)
            Node.__type_sequences[cls] = types = tuple(seq)
        return types


class SequenceNode(Generic[TAG, N], Sequence, Node[TAG], ABC):
    seq: 'Tuple[N, ...]'

    def _parse(self) -> 'None':
        self.__node_list: 'List[N]' = []
        self._parse_seq()
        self.seq = tuple(self.__node_list)

    @abstractmethod
    def _parse_seq(self) -> 'None':
        pass

    def _append(self, node: 'N') -> 'None':
        self.__node_list.append(node)

    def __len__(self) -> 'int':
        return len(self.seq)

    def __getitem__(self, index):
        return self.seq[index]


# -----------------------------------------------------------------------------


R = TypeVar('R')


class Visitor(Generic[TAG, R]):
    def _visit(self, node: 'Node[TAG]', *args) -> 'R':
        suffix = "" if node.is_consistent else "_inconsistent"
        for κ in reversed(node.types):
            if issubclass(κ, Node):
                method_name = f"_visit{suffix}_{Visitor.__get_name(κ)}"
                method = getattr(self, method_name, None)
                if method is not None:
                    return method(node, *args)
        raise AssertionError("method not found")

    __names: 'MutableMapping[type, str]' = {}

    @staticmethod
    def __get_name(cls: 'type') -> 'str':
        name = Visitor.__names.get(cls)
        if name is None:
            cls_name = cls.__name__
            start, words = 0, []
            for i, c in enumerate(cls_name):
                if c.isupper() and i != 0:
                    words.append(cls_name[start:i])
                    start = i
            words.append(cls_name[start:])

            name = "_".join(map(str.lower, words))
            Visitor.__names[cls] = name
        return name


class VoidVisitor(Generic[TAG], Visitor[TAG, None]):
    def _visit_inconsistent_node(self, node: 'Node') -> 'None':
        pass


# -----------------------------------------------------------------------------
