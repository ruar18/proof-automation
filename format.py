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
    ensures = ""
    requires = ""
    if func.ensures:
        ensures = f"{Dafny.ENS} " + ", ".join(func.ensures)
    if func.requires:
        requires = f"{Dafny.REQ} " + ", ".join(func.requires)
    body = pp_function_body(func)
    full = signature
    if ensures:
        full += f"\n{ensures}"
    if requires:
        full += f"\n{requires}"
    return_line = pp_return(func)
    full += f"\n{{\n{body}\n{return_line}\n}}"  # TODO: fix indentation
    return full


def pp_return(func: Function) -> str:
    """Return a string representing the return line of the lifted <func>."""
    var_list = [f"{func.name}Res"] + [f"{aux.name}Res" for aux in func.aux]
    return f"({', '.join(var_list)})"


def pp_function_body(func: Function) -> str:
    body = f"{Dafny.VAR} {func.name}Res := ({func.body});"
    inputs = pp_function_inputs(func)
    for aux in func.aux:
        body += f"\n {Dafny.VAR} {aux.name}Res := {aux.name}({inputs});"
    return body


def pp_function_inputs(func: Function) -> str:
    input_params = ""
    for name, _type in zip(func.param_names, func.param_types):
        input_params += f"{name}: {_type}, "
    input_params = input_params[:-2]
    return input_params


def pp_function_signature(func: Function) -> str:
    """Return a string corresponding to the signature of the lifted <func>."""
    input_params = pp_function_inputs(func)
    signature = f"{Dafny.FUNCTION} {func.name}({input_params}): " \
                f"{func.lifted_type}"
    return signature


# Join formatting
def pp_lifted_join(func: Function) -> str:
    """Return a string corresponding to the lifted join of <func>."""
    signature = pp_join_signature(func)
    requires = pp_seq_requires(func, ["a", "b"])
    body = pp_join_body(func)
    full = signature
    return_line = pp_return(func)
    if requires:
        full += f"\n{requires}"
    full += f"\n{{\n{body}\n{return_line}\n}}"  # TODO: fix indentation
    return full


def pp_join_signature(func: Function) -> str:
    """Return the join signature for <func>."""
    _type = func.lifted_type
    return f"{Dafny.FUNCTION} {func.name}Join(a: {_type}, b: {_type}): {_type}"


def pp_all_sequences(func: Function, name: str) -> List[str]:
    """Return a list of strings, each of which represents a sequence
    in the return type of <func>, with parameter name <name>."""
    indices = []
    # If the return type is just (seq<int>):
    if func.lifted_type.is_seq:
        indices.append(f"{name}")
    if func.lifted_type.tuple_type:
        named_indices = [f"{name}.{idx}" for idx in
                         func.lifted_type.get_seq_indices()]
        indices.extend(named_indices)
    return indices


def pp_seq_requires(func: Function, names: List[str]) -> str:
    """Return a string representing the preconditions for the join/associativity
    lemma of <func>, for the parameter names in <names>"""
    requires = f"{Dafny.REQ} "
    sequences = []
    for name in names:
        sequences.extend(pp_all_sequences(func, name))
    requires += " == ".join(f"|{seq}|" for seq in sequences)
    return requires


def pp_join_body(func: Function) -> str:
    """Return a string representing the join body for <func>"""
    body = f"{Dafny.VAR} {func.name}Res := ({func.join_body});"
    # TODO: fix this, it will fail quite badly with indexing into inputs
    for aux in func.aux:
        body += f"\n {Dafny.VAR} {aux.name}Res := ({aux.join_body});"
    return body


# Associativity formatting
def pp_assoc_ensures(func: Function) -> str:
    """Return a string representation of the postcondition of the associativity
    lemma for <func>."""
    join_name = f"{func.name}Join"
    left_assoc = f"{join_name}({join_name}(a, b), c)"
    right_assoc = f"{join_name}(a, {join_name}(b, c))"
    return f"{Dafny.ENS} {left_assoc} == {right_assoc}"


def pp_assoc_decreases(func: Function) -> str:
    """Return a string representation of the "decreases" measure of the
    associativity lemma for <func>."""
    decreases = f"{Dafny.DEC} "
    sequences = []
    for name in ['a', 'b', 'c']:
        sequences.extend(pp_all_sequences(func, name))
    decreases += ", ".join(sequences)
    return decreases


# Homomorphism proof formatting
def pp_hom_proof(func: Function) -> str:
    """Return a string corresponding to the homomorphism proof of the
    Dafny function <func>."""
    signature = pp_hom_signature(func)
    requires = pp_hom_requires()
    ensures = pp_hom_ensures(func)
    base = pp_hom_base_cases()
    induct = pp_hom_induction(func)
    return f"{signature}\n{requires}\n{ensures}\n{{{base}\n{induct}\n}}"


def pp_hom_signature(func: Function) -> str:
    """Return a string corresponding to the signature of the homomorphism proof
    of <func>."""
    return f"{Dafny.LEM} Hom{func.name}(s: {Dafny.SEQ2D}, t: {Dafny.SEQ2D}"


def pp_hom_requires() -> str:
    """Return a string corresponding to the precondition of a homomorphism
    proof."""
    return f"{Dafny.REQ} width(s) == width(t)"


def pp_hom_ensures(func: Function) -> str:
    """Return a string corresponding to the postcondition of a homomorphism
    proof of <func>."""
    return f"{Dafny.ENS} {func.name}(s + t) == " \
           f"{func.name}Join({func.name}(s), {func.name}(t))"


def pp_hom_base_cases() -> str:
    """Return a string corresponding to the empty and singleton base cases
    of a homomorphism proof."""
    # TODO: fix indentation
    base = f"{Dafny.IF} t == [] {{\n"
    base += f"{Dafny.ASRT} s + t == s;"
    base += f"}} {Dafny.ELSEIF} |t| == 1 {{}}"
    return base


def pp_hom_induction(func: Function) -> str:
    """Return a string corresponding to the induction step of the homomorphism
    proof of <func>."""
    induct = f"{Dafny.ELSE}{{\n{Dafny.VAR} t1 := t[..|t|-1];\n"
    induct += f"{Dafny.VAR} t2 := [t[|t|-1]];\n"
    induct += f"{Dafny.ASRT} (s + t1) + t2 == s + t;\n"
    name = func.name
    induct += f"{name}JoinAssoc({name}(s), {name}(t1), {name}(t2));\n}}"
    return induct
