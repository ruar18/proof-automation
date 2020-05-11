"""
Represent a Dafny program in Python.
"""
from __future__ import annotations

from typing import List, Dict


class Dafny:
    """Represents Dafny keywords and types."""
    FUNCTION = "function"
    REQ = "requires"
    ENS = "ensures"
    DEC = "decreases"
    VAR = "var"
    SEQ = "seq<int>"
    SEQ2D = "seq2D"
    INT = "int"
    IF = "if"
    ELSEIF = "else if"
    ELSE = "else"
    AND = "&&"
    ASRT = "assert"
    LEM = "lemma"


class Function:
    """A Dafny function.

    === Public Attributes ===
    name:
        The name of the Dafny function.
    param_names:
        The names of the parameters of the function.
    param_types:
        The types of the parameters of the function.
    return_type:
        The (unlifted) return type of the Dafny function.
    lifted_type:
        The lifted return type of the Dafny function.
    decreases:
        Decrease measure for the function definition.
    requires:
        A list of the "requires" statements of the function.
    ensures:
        A list of the "ensures" statements of the function.
    aux:
        A list of Dafny functions needed for the join of this function.
    body:
        The body of the (unlifted) Dafny function.
    join_body:
        The body of the (unlifted) join for the function.
    """
    name: str
    param_names: List[str]
    param_types: List[Type]
    return_type: Type
    lifted_type: Type
    decreases: List[str]
    requires: List[str]
    ensures: List[str]
    aux: List[Function]
    body: str
    join_body: str

    def __init__(self, name: str, param_names: List[str],
                 param_types: List[Type], return_type: Type,
                 decreases: List[str], requires: List[str], ensures: List[str],
                 aux: List[Function], body: str, join_body: str) -> None:
        """Initialize this Function with the given information."""
        self.name = name
        self.param_names = param_names
        self.param_types = param_types
        self.return_type = return_type
        self.decreases = decreases
        self.requires = requires
        self.ensures = ensures
        self.aux = aux
        self.body = body
        self.join_body = join_body
        self.__set_lifted__type()

    def __set_lifted__type(self) -> None:
        """Compute and set the lifted type for this Function."""
        # If the function does not need to be lifted
        if not self.aux:
            self.lifted_type = self.return_type
        else:
            aux_types = [func.lifted_type for func in self.aux]
            self.lifted_type = Type([self.return_type] + aux_types)

    def flatten_data(self, prefixes: List[str]) -> Dict[str, str]:
        """Return a dictionary of pairs (<indexing>, <name>), where <indexing>
        represents the index into an object of type <self.lifted_type>, and
        <name> is the name of the function computing the corresponding datum.
        <prefixes> are prepended to index properly."""
        cur_unlifted = 0
        data = {f"{'.'.join(prefixes + [str(cur_unlifted)])}": self.name}
        for i, aux in enumerate(self.aux):
            cur_unlifted += 1
            # If this aux is not lifted:
            if not aux.aux:
                data[f"{'.'.join(prefixes + [str(cur_unlifted)])}"] = aux.name
            else:
                data.update(aux.flatten_data(prefixes + [str(i + 1)]))
        return data

    def __str__(self) -> str:
        """Return a string representation of this Function."""
        if not self.aux:
            return self.name
        return f"({self.name}, {', '.join(str(aux) for aux in self.aux)})"


class Variable:
    """A Dafny variable or input parameter.

    === Public Attributes ===
    name:
        The name of the variable.
    _type:
        The type of the variable.
    """
    name: str
    _type: Type

    def __init__(self, name: str, _type: Type) -> None:
        """Initialize this Variable with the given information."""
        self.name = name
        self._type = _type


class Type:
    """A Dafny type.

    === Public Attributes ===
    type:
        A list of Types, representing a tuple of Dafny types.
    simple_type:
        If this Type is not a tuple of types, this is its type.
    is_seq:
        Indicates whether this Type is a seq<int> or (seq<int>) type
    is_int:
        Indicates whether this Type is an int or (int) type
    === Representation Invariants ===
        - tuple_type is empty if and only if simple_type is not empty.
        - is_seq is True if and only if simple_type is equal to "seq<int>"
    """
    tuple_type: List[Type]
    simple_type: str
    is_seq: bool
    is_int: bool

    def __init__(self, tuple_type: List[Type], simple_type="") -> None:
        self.tuple_type = tuple_type
        self.simple_type = simple_type
        self.is_seq = simple_type == Dafny.SEQ or \
                      (len(tuple_type) == 1 and tuple_type[0].is_seq)
        self.is_int = simple_type == Dafny.INT or \
                      (len(tuple_type) == 1 and tuple_type[0].is_int)

    def __str__(self) -> str:
        """Return the string representation of this Type."""
        if self.simple_type:
            return f"{self.simple_type}"
        return f"({', '.join(map(str, self.tuple_type))})"

    def get_seq_indices(self) -> List[str]:
        """If <tuple_type> is nonempty, return a list of strings indexing
        into every sequence in this Type. Otherwise, return an empty list."""
        indices = []
        for i, _type in enumerate(self.tuple_type):
            # If this Type is a seq<int> type:
            if _type.is_seq:
                indices.append(str(i))
            # Otherwise, recursively get the indices:
            elif not _type.is_int:
                cur_indices = [f"{i}.{idx}" for idx in _type.get_seq_indices()]
                indices.extend(cur_indices)
        return indices
