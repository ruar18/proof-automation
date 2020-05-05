"""
Parse Dafny input and represent it with an S-expression.
"""
from __future__ import annotations
from typing import List


def parse_function(func: str) -> str:
    """Convert a string <func> that contains the definition of a Dafny function
    into an S-expression representing the function."""