"""
Functions to format a homomorphism proof for a given Dafny function.
"""
from __future__ import annotations

import textwrap
from typing import List

from dafny import Dafny, Function, Type

INDENT_AMOUNT = 4


# Line indenting
def indent(s: str) -> str:
    return textwrap.indent(s, INDENT_AMOUNT * " ")


# Function formatting
def pp_lifted_function(func: Function) -> str:
    """Return a string corresponding to the lifted version of <func>."""
    signature = pp_function_signature(func)
    full = signature
    if func.decreases:
        decreases = indent(f"{Dafny.DEC} " + ", ".join(func.decreases))
        full += f"\n{decreases}"
    if func.ensures:
        ensures = indent(f"{Dafny.ENS} " + ", ".join(func.ensures))
        full += f"\n{ensures}"
    if func.requires:
        requires = indent(f"{Dafny.REQ} " + ", ".join(func.requires))
        full += f"\n{requires}"
    body = indent(pp_function_body(func))
    return_line = indent(pp_return(func))
    full += f"\n{{\n{body}\n{return_line}\n}}"
    return full


def pp_return(func: Function) -> str:
    """Return a string representing the return line of the lifted <func>."""
    var_list = [f"{func.name}Res"] + [f"{aux.name}Res" for aux in func.aux]
    return f"({', '.join(var_list)})"


def pp_function_body(func: Function) -> str:
    """Return a string representing the body of the lifted <func>."""
    body = f"{Dafny.VAR} {func.name}Res := ({func.body});"
    inputs = pp_function_inputs(func, print_type=False)
    for aux in func.aux:
        body += f"\n{Dafny.VAR} {aux.name}Res := {aux.name}({inputs});"
    return body


def pp_function_inputs(func: Function, print_type=True) -> str:
    """Return a string representing the inputs to <func>, as they would appear
    in the function's signature. If <print_type> is False, the input types
    are not printed."""
    input_params = ""
    for name, _type in zip(func.param_names, func.param_types):
        if print_type:
            input_params += f"{name}: {_type}, "
        else:
            input_params += f"{name}, "
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
    body = indent(pp_join_body(func))
    full = signature
    return_line = indent(pp_return(func))
    if requires:
        full += indent(f"\n{Dafny.REQ} {requires}")
    full += f"\n{{\n{body}\n{return_line}\n}}"
    return full


def pp_join_signature(func: Function) -> str:
    """Return the join signature for <func>."""
    _type = func.lifted_type
    a, b = func.join_param_names
    return f"{Dafny.FUNCTION} {func.name}Join({a}: {_type}, " \
           f"{b}: {_type}): {_type}"


def pp_all_sequences(func: Function, name: str) -> List[str]:
    """Return a list of strings, each of which represents a sequence
    in the return type of <func>, with parameter name <name>."""
    indices = []
    # If the return type is just (seq<int>):
    if func.lifted_type.is_seq:
        indices.append(f"{name}")
    elif func.lifted_type.tuple_type:
        named_indices = [f"{name}.{idx}" for idx in
                         func.lifted_type.get_seq_indices()]
        indices.extend(named_indices)
    return indices


def pp_seq_requires(func: Function, names: List[str]) -> str:
    """Return a string representing the preconditions for the join/associativity
    lemma of <func>, for the parameter names in <names>"""
    requires = ""
    sequences = []
    for name in names:
        sequences.extend(pp_all_sequences(func, name))
    requires += " == ".join(f"|{seq}|" for seq in sequences)
    return requires


def pp_join_body(func: Function) -> str:
    """Return a string representing the join body for <func>."""
    body = f"{Dafny.VAR} {func.name}Res := ({func.join_body});"
    a, b = func.join_param_names
    for i, aux in enumerate(func.aux):
        body += f"\n{Dafny.VAR} {aux.name}Res := " \
                f"{aux.name}Join({a}.{i + 1}, {b}.{i + 1});"
    return body


# Associativity formatting
def pp_assoc_requires(func: Function) -> str:
    """Return a string representation of the part of the precondition that is
    specific to the associativity proof; namely, a list of strings representing
    that two elements of an argument are identically equal, all joined by
    conjunction."""
    equalities = []
    data = func.flatten_data([])
    for index_i, name_i in data.items():
        for index_j, name_j in data.items():
            if index_i != index_j and index_i < index_j and name_i == name_j:
                equalities.append(f"a.{index_i} == a.{index_j}")
    if not equalities:
        return ""
    else:
        full = f" {Dafny.AND} {(' ' + Dafny.AND + ' ').join(equalities)}"
        # The preconditions are symmetric with respect to parameter name
        return full + "".join(full.replace("a", name) for name in ["b", "c"])


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
    decreases += ", ".join(f"|{seq}|" for seq in sequences)
    return decreases


def pp_assoc_signature(func: Function) -> str:
    """Return a string representation of the signature of the associativity
    lemma for <func>."""
    _type = func.lifted_type
    return f"{Dafny.LEM} {func.name}JoinAssoc" \
           f"(a: {_type}, b: {_type}, c: {_type})"


def pp_assoc_base_case(func: Function) -> str:
    """Return a string representation of the base case of the associativity
    lemma for <func>."""
    sequences = pp_all_sequences(func, "a")
    return f"{Dafny.IF} |{sequences[0]}| == 0 {{}}\n" \
           f"{Dafny.ELSEIF} |{sequences[0]}| == 1 {{}}"


def pp_assoc_slices(func: Function, name: str) -> str:
    """Return a string representation of variable declarations corresponding
    to slices of all sequences in the parameter <name>."""
    sequences = pp_all_sequences(func, name)
    slices = ""
    for seq in sequences:
        # Remove all periods from the slice name
        slice_name = seq.replace(".", "") + "'"
        slices += f"{Dafny.VAR} {slice_name} := {seq}[..|{seq}|-1];\n"
    return slices


def pp_assoc_finals(func: Function, name: str) -> str:
    """Return a string representation of variable declarations corresponding
    to the final element of all sequences in the parameter <name>."""
    sequences = pp_all_sequences(func, name)
    finals = ""
    for seq in sequences:
        # Remove all periods from the slice name
        final_name = seq.replace(".", "") + "f"
        finals += f"{Dafny.VAR} {final_name} := [{seq}[|{seq}|-1]];\n"
    return finals


def pp_assoc_construct(_type: Type, name: str, prefixes: List[str],
                       suffix: str) -> str:
    """Return a string representation of an object of type <_type>,
    using slices/final elements of sequences in the parameter <name>.
    <prefixes> is  a list of strings prepended in front of the results, as
    required by the recursion. <suffix> indicates whether the object is
    constructed from slices or final elements."""
    # Base case
    if len(_type.tuple_type) <= 1:
        if str(_type.tuple_type[0]) == Dafny.INT:
            return f"({'.'.join(prefixes)})"
        # Otherwise, a sequence type, which has been sliced
        else:
            return f"{''.join(prefixes)}{suffix}"
    # Recursion
    else:
        results = []
        for i, aux in enumerate(_type.tuple_type):
            results.append(pp_assoc_construct(aux, name, prefixes + [str(i)],
                                              suffix))
        return f"({', '.join(results)})"


def pp_assoc_recursive_call(func: Function, suffix: str) -> str:
    """Return a string representation of the recursive call used in the
    induction step of the associativity proof. <suffix> is "'" if we recurse on
    sequence slices, and "f" if we recurse on final elements of sequences."""
    result = f"({pp_assoc_construct(func.lifted_type, 'a', ['a'], suffix)})"
    # The construction is symmetric with respect to parameter name
    results = [result] + [result.replace("a", name) for name in ["b", "c"]]
    return f"{func.name}JoinAssoc({', '.join(results)});\n"


def pp_assoc_induction(func: Function) -> str:
    """Return a string representation of the induction step of the associativity
    lemma for <func>."""
    induct = f"{Dafny.ELSE}\n{{\n"
    # Declare slices
    for name in ["a", "b", "c"]:
        induct += indent(pp_assoc_slices(func, name))
    induct += indent(pp_assoc_recursive_call(func, "'") + "\n")
    for name in ["a", "b", "c"]:
        induct += indent(pp_assoc_finals(func, name))
    induct += indent(pp_assoc_recursive_call(func, "f"))
    return induct + "}\n"


def pp_assoc_proof(func: Function) -> str:
    """Return a string representation of the associativity lemma for <func>."""
    signature = pp_assoc_signature(func)
    ensures = indent(pp_assoc_ensures(func))
    # If the function does not return any sequence:
    if not func.lifted_type.get_seq_indices():
        return f"{signature}\n{ensures}\n{{\n}}"
    decreases = indent(pp_assoc_decreases(func))
    requires = indent(f"{Dafny.REQ} {pp_seq_requires(func, ['a', 'b', 'c'])}"
                      f" {pp_assoc_requires(func)}")
    base = indent(pp_assoc_base_case(func))
    induct = indent(pp_assoc_induction(func))
    return f"{signature}\n{decreases}\n{requires}\n{ensures}\n" \
           f"{{\n{base}\n{induct}}}"


# Homomorphism proof formatting
def pp_hom_proof(func: Function) -> str:
    """Return a string corresponding to the homomorphism proof of the
    Dafny function <func>."""
    signature = pp_hom_signature(func)
    requires = indent(pp_hom_requires(func))
    ensures = indent(pp_hom_ensures(func))
    base = indent(pp_hom_base_cases())
    induct = indent(pp_hom_induction(func))
    if requires:
        return f"{signature}\n{requires}\n{ensures}\n{{\n{base}\n{induct}\n}}"
    return f"{signature}\n{ensures}\n{{\n{base}\n{induct}\n}}"


def pp_hom_signature(func: Function) -> str:
    """Return a string corresponding to the signature of the homomorphism proof
    of <func>."""
    return f"{Dafny.LEM} Hom{func.name}(s: {func.param_types[0]}, " \
           f"t: {func.param_types[0]})"


def pp_hom_requires(func: Function) -> str:
    """Return a string corresponding to the precondition of a homomorphism
    proof."""
    if func.param_types[0] == Dafny.SEQ2D:
        return f"{Dafny.REQ} width(s) == width(t)"
    return ""


def pp_hom_ensures(func: Function) -> str:
    """Return a string corresponding to the postcondition of a homomorphism
    proof of <func>."""
    return f"{Dafny.ENS} {func.name}(s + t) == " \
           f"{func.name}Join({func.name}(s), {func.name}(t))"


def pp_hom_base_cases() -> str:
    """Return a string corresponding to the empty and singleton base cases
    of a homomorphism proof."""
    base = f"{Dafny.IF} t == [] \n{{\n"
    base += indent(f"{Dafny.ASRT} s + t == s;\n")
    base += f"}}\n{Dafny.ELSEIF} |t| == 1 \n{{\n}}"
    return base


def pp_hom_induction(func: Function) -> str:
    """Return a string corresponding to the induction step of the homomorphism
    proof of <func>."""
    induct = f"{Dafny.ELSE}\n{{\n"
    induct += indent(f"{Dafny.VAR} t1 := t[..|t|-1];\n")
    induct += indent(f"{Dafny.VAR} t2 := [t[|t|-1]];\n")
    induct += indent(f"{Dafny.ASRT} (s + t1) + t2 == s + t;\n")
    name = func.name
    induct += indent(f"Hom{name}(s, t1);\n")
    induct += indent(f"{name}JoinAssoc({name}(s), {name}(t1), {name}(t2));\n")
    induct += "}"
    return induct
