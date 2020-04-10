"""
Functions to format a homomorphism proof for a given Dafny function.
"""
from __future__ import annotations
from typing import List, Optional, Union, TextIO
from dafny import Dafny, Function


# Function formatting
def pp_lifted_function(func: Function) -> str:
    """Return a string corresponding to the lifted version of <func>."""
    signature = pp_function_signature(func)
    ensures = ", ".join(func.ensures)
    requires = ", ".join(func.requires)
    body = pp_function_body(func)
    full = signature
    if ensures:
        full += f"\n{ensures}"
    if requires:
        full += f"\n{requires}"
    full += f"\n{{\n{body}\n}}"  # TODO: fix indentation
    return full


def pp_function_body(func: Function) -> str:
    body = f"{Dafny.VAR} {func.name}Res := ({func.body})"
    for aux in func.aux:
        body += f"\n {Dafny.VAR} {aux.name}Res := ({aux.body})"
    return body


def pp_function_signature(func: Function) -> str:
    """Return a string corresponding to the signature of the lifted <func>."""
    input_params = ""
    for name, _type in zip(func.param_names, func.param_types):
        input_params += name + ": " + str(_type)
    input_params = input_params[:-1]
    signature = f"{Dafny.FUNCTION} {func.name}({input_params}): " \
                f"{func.lifted_type}"
    return signature


# Join formatting
def pp_lifted_join(func: Function) -> str:
    """Return a string corresponding to the lifted join of <func>."""
    signature = pp_join_signature(func)
    requires = pp_join_requires(func)
    body = pp_join_body(func)
    full = signature
    if requires:
        full += f"\n{requires}"
    full += f"\n{{\n{body}\n}}"  # TODO: fix indentation
    return full


def pp_join_signature(func: Function) -> str:
    """Return the join signature for <func>."""
    _type = func.lifted_type
    return f"{Dafny.FUNCTION} {func.name}Join(a: {_type}, b: {_type}): {_type}"


def pp_join_requires(func: Function) -> str:
    """Return a string representing the preconditions for the join of <func>."""
    requires = f"{Dafny.REQ} "
    # A list of all sequence indices in the return type of <func>
    all_seq = []
    for i, name, _type in enumerate(zip(func.param_names, func.param_types)):
        # If the current parameter is an untupled seq<int>:
        if _type.is_seq == Dafny.SEQ:
            all_seq.append(f"|{name}|")
        # TODO: rest


def pp_join_body(func: Function) -> str:
    body = f"{Dafny.VAR} {func.name}Res := ({func.join_body})"
    for aux in func.aux:
        body += f"\n {Dafny.VAR} {aux.name}Res := ({aux.join_body})"
    return body


# Associativity formatting
def pp_assoc_ensures(func: Function) -> str:
    """Return a string representation of the postcondition of the associativity
    lemma for <func>."""
    pass


# Homomorphism proof formatting
def pp_hom_proof(func: Function) -> str:
    """Return a string corresponding to the homomorphism proof of the
    Dafny function <func>."""
    pass


def pp_hom_requires() -> str:
    """Return a string corresponding to the precondition of a homomorphism
    proof."""
    return "requires width(s) == width(t)"
