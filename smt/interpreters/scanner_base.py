from typing import Any, Union, Optional, Set, Iterator, TypeVar, Generic, Callable
from abc import ABC, abstractmethod
from functools import total_ordering


# -----------------------------------------------------------------------------


@total_ordering
class Position:
    """ Location within text being scanned by lexical analyzer.

        Position object encapsulates both input text and coordinates within it
        (offset, line number, column number).
        It is immutable, so moving along the text results in creation of
        new Position objects.

        Positions are hashable and comparable.
    """

    def __init__(self, filename: 'str', text: 'str', offs: 'int', line: 'int', col: 'int') -> 'None':
        """ Private constructor, should not be called outside the class.
            Use `beginning_of` method instead.
        """
        self.__filename, self.__text = filename, text
        self.__offs, self.__line, self.__col = offs, line, col

    @property
    def filename(self) -> 'str':
        """ Returns the name of file from which input text was loaded.
        """
        return self.__filename

    @property
    def offs(self) -> 'int':
        """ Returns offset in characters from the beginning of input text (starting at 0).
        """
        return self.__offs

    @property
    def line(self) -> 'int':
        """ Returns line number (starting at 1).
        """
        return self.__line

    @property
    def col(self) -> 'int':
        """ Returns column number (starting at 1).
        """
        return self.__col

    @staticmethod
    def beginning_of(filename: 'str', text: 'Optional[str]' = None) -> 'Position':
        """ Returns the position representing the beginning of text in the specified file.
            If `text` parameter is not provided, the file contents are loaded from disk.
        """
        if text is None:
            f = open(filename)
            text = f.read()
            f.close()
        return Position(filename, text, 0, 1, 1)

    EOF = chr(0x10FFFF)

    @property
    def ch(self) -> 'str':
        """ Returns current character (or `Position.EOF` on end of file).
        """
        return self.__text[self.offs] if self.offs < len(self.__text) else Position.EOF

    @property
    def next(self) -> 'Position':
        """ Returns new position that immediately follows the current one.
        """
        if self.ch == Position.EOF:
            return self
        elif self.ch == '\n':
            return Position(self.filename, self.__text, self.offs + 1, self.line + 1, 1)
        else:
            return Position(self.filename, self.__text, self.offs + 1, self.line, self.col + 1)

    def skip(self, n: 'int') -> 'Position':
        """ Returns new position that is obtained by skipping `n` sequential
            characters beginning from the current one. If there are less than
            'n' characters left in the input buffer, the returned position
            will point past the end of file.
        """
        pos = self
        while pos.ch != Position.EOF and n > 0:
            pos = pos.next
            n -= 1
        return pos

    def get_image(self, follow: 'Position') -> 'str':
        """ Returns the substring of input text from current position till
            `follow` position, not including the character at `follow` position.
        """
        assert (self.filename == follow.filename) and (self <= follow)
        return self.__text[self.offs: follow.offs]

    def __eq__(self, other) -> 'bool':
        return (self.filename, self.offs) == (other.filename, other.offs)

    def __le__(self, other) -> 'bool':
        return (self.filename, self.offs) <= (other.filename, other.offs)

    def __hash__(self) -> 'int':
        return hash((self.filename, self.offs))

    def __str__(self) -> 'str':
        return f"({self.line}, {self.col})"


# -----------------------------------------------------------------------------


@total_ordering
class Message(Exception):
    """ Error message tied to the position in text.

        Messages are hashable and comparable. (At first two messages are
        compared by position, then by description.)

        Messages may be raised as exceptions. It is useful to interrupt
        recursive descent parsers.
    """

    def __init__(self, pos: 'Position', description: 'str') -> 'None':
        """ Creates new error message tied to the specified `pos`
            with given `description`.
        """
        self.__pos, self.__description = pos, description

    @property
    def pos(self) -> 'Position':
        """ Returns the position, that error message is tied to.
        """
        return self.__pos

    @property
    def description(self) -> 'str':
        """ Returns the description of error message.
        """
        return self.__description

    def __eq__(self, other) -> 'bool':
        return (self.pos, self.description) == (other.pos, other.description)

    def __le__(self, other) -> 'bool':
        return (self.pos, self.description) <= (other.pos, other.description)

    def __hash__(self) -> 'int':
        return hash((self.pos, self.description))

    def __str__(self) -> 'str':
        return f"{self.pos}: {self.description}"


class MessageSet:
    """ Collection of error messages.

        Iterator of MessageSet gives sorted sequence of messages,
        suitable for output into error log.
    """

    def __init__(self) -> 'None':
        self.__messages: 'Set[Message]' = set()

    def add(self, msg: 'Message') -> 'None':
        """ Adds new message to the collection.
        """
        self.__messages.add(msg)

    def clear(self) -> 'None':
        """ Empties the collection.
        """
        self.__messages.clear()

    def __len__(self) -> 'int':
        return len(self.__messages)

    def __iter__(self) -> 'Iterator[Message]':
        return iter(sorted(self.__messages))

    def __repr__(self) -> 'str':
        return f"MessageSet({len(self)} messages)"


# -----------------------------------------------------------------------------


TAG = TypeVar('TAG')


class AbstractScanner(ABC, Generic[TAG]):
    """ Abstract base class for lexical scanners.

        Lexical scanner is a mutable object, whose state contains
        current position in the input text, current token and
        a collection of error messages.

        Current token is represented by its `tag` and coordinates
        (`start` and `follow` positions).
    """

    def __init__(self, pos: 'Position', ms: 'MessageSet') -> 'None':
        self.__start: 'Optional[Position]' = None
        self.__follow = pos
        self.__ms = ms
        self.__tag = self._scan()

    @abstractmethod
    def _scan(self) -> 'Optional[TAG]':
        pass

    @property
    def start(self) -> 'Position':
        assert self.__start is not None
        return self.__start

    @property
    def follow(self) -> 'Position':
        assert self.__start is not None
        return self.__follow

    @property
    def tag(self) -> 'Optional[TAG]':
        assert self.__start is not None
        return self.__tag

    @property
    def image(self) -> 'str':
        assert self.__start is not None
        return self.__start.get_image(self.__follow)

    def read_token(self) -> 'None':
        self.__start = None
        self.__tag = self._scan()

    def report(self, description: 'str', at_start: 'bool' = False) -> 'Message':
        msg = Message(self.start if at_start else self.__follow, description)
        self.__ms.add(msg)
        return msg

    def _consume(self, criterion: 'MatchCriterion') -> 'bool':
        if _satisfies(self.__follow.ch, criterion):
            self.__follow = self.__follow.next
            return True
        return False

    def _consume_while(self, criterion: 'MatchCriterion') -> 'None':
        while self.__follow.ch != Position.EOF:
            if not self._consume(criterion):
                break

    def _consume_until(self, criterion: 'MatchCriterion') -> 'None':
        self._consume_while(lambda c: not _satisfies(c, criterion))

    def _consume_invalid_char(self) -> 'None':
        self.report(f"invalid character {repr(self.__follow.ch)}")
        self.__follow = self.__follow.next

    def _mark_start(self) -> 'None':
        self.__start = self.__follow


MatchCriterion = Union[str, Callable[[str], Any]]


def _satisfies(ch: 'str', criterion: 'MatchCriterion') -> 'bool':
    return ch in criterion if isinstance(criterion, str) else criterion(ch)


# -----------------------------------------------------------------------------
