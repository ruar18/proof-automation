"""
Represent a Dafny program in Python.
"""
from __future__ import annotations
from typing import List, Optional, Union, TextIO


class Dafny:
    """Represents Dafny keywords."""
    FUNCTION = "function"
    REQ = "requires"
    VAR = "var"
    SEQ = "seq<int>"


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
    requires: List[str]
    ensures: List[str]
    aux: List[Function]
    body: str
    join_body: str

    def __init__(self, name: str, param_names: List[str],
                 param_types: List[Type],
                 return_type: Type, requires: List[str], ensures: List[str],
                 aux: List[Function], body: str, join_body: str) -> None:
        """Initialize this Function with the given information."""
        self.name = name
        self.param_names = param_names
        self.param_types = param_types
        self.return_type = return_type
        self.__set_lifted__type()
        self.requires = requires
        self.ensures = ensures
        self.aux = aux
        self.body = body
        self.join_body = join_body

    def __set_lifted__type(self) -> None:
        """Compute and set the lifted type for this Function."""
        # If the function does not need to be lifted
        if not self.aux:
            self.lifted_type = self.return_type
        aux_types = [func.lifted_type for func in self.aux]
        self.lifted_type = Type([self.return_type] + aux_types)


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
        Indicates whether this Type is a simple seq<int> type

    === Representation Invariants ===
        - tuple_type is empty if and only if simple_type is not empty.
        - is_seq is True if and only if simple_type is equal to "seq<int>"
    """
    tuple_type: List[Type]
    simple_type: str
    is_seq: bool

    def __init__(self, tuple_type: List[Type], simple_type="") -> None:
        self.tuple_type = tuple_type
        self.simple_type = simple_type
        self.is_seq = (simple_type == "seq<int>")

    def __str__(self) -> str:
        """Return the string representation of this Type."""
        if self.simple_type:
            return self.simple_type
        return f"({', '.join(map(str, self.tuple_type))})"

    def get_seq_indices(self) -> List[str]:
        """If <tuple_type> is nonempty, return a list of strings indexing
        into every sequence in this Type. Otherwise, return an empty list."""
        indices = []
        for i, _type in enumerate(self.tuple_type):
            # If this Type is a seq<int> type (not tupled further):
            if _type.simple_type == Dafny.SEQ:
                indices.append(str(i))
            # Otherwise, recursively get the indices:
            cur_indices = [f"{i}.{idx}" for idx in _type.get_seq_indices()]
            indices.extend(cur_indices)
        return indices
