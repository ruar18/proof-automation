"""
Functions to format a homomorphism proof for a given Dafny function.
"""
from __future__ import annotations
from typing import List, Optional, Union, TextIO
from dafny import Dafny, Function


def pp_lifted_function(func: Function) -> str:
    """Return a string corresponding to the lifted version of <func>."""
    signature = pp_function_signature(func)
    ensures = ", ".join(func.ensures)
    requires = ", ".join(func.requires)
    body = f"{Dafny.VAR} {func.name}Res := ({func.body})"
    for aux in func.aux:
        body += f"\n {Dafny.VAR} {aux.name}Res := ({aux.body})"
    full = signature
    if ensures:
        full += f"\n{ensures}"
    if requires:
        full += f"\n{requires}"
    full += f"\n{{\n{body}\n}}"  # TODO: fix indentation
    return full


def pp_function_signature(func: Function) -> str:
    """Return a string corresponding to the signature of the lifted <func>."""
    input_params = ""
    for name, _type in zip(func.param_names, func.param_types):
        input_params += name + ": " + _type
    input_params = input_params[:-1]
    return_type = pp_function_return_type(func)
    signature = f"{Dafny.FUNCTION} {func.name}({input_params}): " \
                f"{return_type}"
    return signature


def pp_function_return_type(func: Function) -> str:
    """Return a string corresponding to the lifted return type of <func>."""
    if not func.aux:
        return func.return_type
    # A comma-separated list of the return types for each aux
    return_for_aux = ", ".join(map(pp_function_return_type, func.aux))
    return_type = f"({func.return_type}, {return_for_aux})"
    return return_type


def pp_hom_proof(func: Function) -> str:
    """Return a string corresponding to the homomorphism proof of the
    Dafny function <func>."""
    pass


def pp_hom_requires() -> str:
    """Return a string corresponding to the precondition of a homomorphism
    proof."""
    return "requires width(s) == width(t)"
