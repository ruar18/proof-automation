"""Functions to print the proofs for the given Dafny functions."""
from __future__ import annotations
from typing import List, Callable
from dafny import Dafny, Function, Type
from format import pp_lifted_function, pp_lifted_join, pp_assoc_proof, \
    pp_hom_proof

all_components = [pp_lifted_function, pp_lifted_join, pp_assoc_proof,
                  pp_hom_proof]


def print_result(file_name: str, funcs: List[Function],
                 to_call: Callable) -> None:
    """Print the result of calling <to_call> on each function in <funcs>,
    to the file named <file_name>."""
    f = open(file_name, "a")
    for func in funcs:
        result = to_call(func)
        if result:
            f.write(to_call(func) + "\n\n")


def print_all(file_name: str, funcs: List[Function]) -> None:
    """Print the result of calling all proof components on each function in
    <funcs>, to the file named <file_name>."""
    # Clear the previous output
    open(file_name, "w")
    for component in all_components:
        print_result(file_name, funcs, component)
