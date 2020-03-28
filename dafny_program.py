"""
Represent a Dafny program in Python.
"""
from __future__ import annotations
from typing import List, Optional, Union, TextIO


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
        The return type of the Dafny function.
    requires:
        A list of the "requires" statements of the function.
    ensures:
        A list of the "ensures" statements of the function.
    aux:
        A list of Dafny functions needed for the join of this function.
    body:
        The body of the Dafny function.
    """
    name: str
    param_names: List[str]
    param_types: List[str]
    return_type: str
    requires: List[str]
    ensures: List[str]
    aux: List[Function]
    body: str

    def __init__(self, name: str, param_names: List[str],
                 param_types: List[str],
                 return_type: str, requires: List[str], ensures: List[str],
                 aux: List[Function], body: str) -> None:
        """Initialize this Function with the given information."""
        self.name = name
        self.param_names = param_names
        self.param_types = param_types
        self.return_type = return_type
        self.requires = requires
        self.ensures = ensures
        self.aux = aux
        self.body = body
