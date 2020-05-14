"""
Load a Dafny program from S-expressions representing the program.
"""
from typing import List, Union, Any, Dict

from sexpdata import Symbol, loads

from dafny import Function, Type, Dafny
from proof_print import print_all


def generate_proof(input_name: str, output_name: str) -> None:
    """Given a file <input_name> with a valid S-expression representation of
    Dafny functions, write the homomorphism proof for each function in the file
    <output_name>."""
    f = open(input_name, "r")
    contents = f"({f.read()})".replace('{', '"').replace('}', '"')
    parsed = loads(contents)
    aux_dict = _read_functions(parsed[0])
    funcs = []
    for definition in parsed[1:]:
        cur_func = _load_function(definition, avail_aux=funcs, indices=aux_dict)
        funcs.append(cur_func)

    for name in aux_dict:
        if name not in aux_dict:
            print(f"Function {name} was not defined.")

    print_all(output_name, funcs)


def _read_functions(func_list: List[Union[List[Any], Symbol, str]]) \
        -> Dict[str, int]:
    """Construct a dictionary of (name, index) pairs from the parsed
    S-expression <func_list> representing a list of functions.
    Format of <func_list>:
    ["functions", <functions>]
    """
    return {name.value(): i for (i, name) in enumerate(func_list[1:])}


def _get_strings(lst: List[Symbol]) -> List[str]:
    """Given a list of Symbols, return a list of corresponding strings."""
    return [symbol.value() for symbol in lst]


def _load_function(func_exp: List[Union[List[Any], Symbol, str]],
                   avail_aux: List[Function], indices: Dict[str, int]) \
        -> Function:
    """Construct a Dafny Function from the parsed S-expression <func_exp>
    representing the function definition. <avail_aux> is a list of functions
    that have already been defined, and <indices> is a dictionary of
    (name, index) pairs, where the indices are into <avail_aux>.
    Format of <func_exp>:
    ["definition", <name>,
        ["type", [<param_types>], <return_type>],
        ["body", ["function", [<param_names>], <body>]],
        ["join", ["function", [<join_param_names>], <join_body>]],
        ["decreases", [<decreases>]],
        ["requires", [<requires>]],
        ["ensures", [<ensures>]],
        ["aux", [<aux>]]
    ]
    """
    try:
        name = func_exp[1].value()
        param_types = [eval(symbol.value()) for symbol in func_exp[2][1]]
        param_names = _get_strings(func_exp[3][1][1])
        return_type = Type([Type([], eval(func_exp[2][2].value()))])
        decreases = func_exp[5][1]
        requires = func_exp[6][1]
        ensures = func_exp[7][1]
        aux_names = _get_strings(func_exp[8][1])
        body = func_exp[3][1][2]
        join_param_names = _get_strings(func_exp[4][1][1])
        join_body = func_exp[4][1][2]
        aux = []
        for cur in aux_names:
            aux.append(avail_aux[indices[cur]])
    except IndexError:
        print(f"Unrecognized input format.")
    else:
        return Function(name, param_names, param_types, return_type,
                        decreases, requires, ensures, aux, body,
                        join_param_names, join_body)
