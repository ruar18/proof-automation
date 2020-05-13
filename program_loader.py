"""
Load a Dafny program from S-expressions representing the program.
"""
from typing import List, Union, Any, Dict
from dafny import Function, Type, Dafny
from sexpdata import Symbol, loads
from proof_print import print_all


def generate_proof(input_name: str, output_name: str) -> None:
    """Given a file <input_name> with a valid S-expression representation of
    Dafny functions, write the homomorphism proof for each function in the file
    <output_name>."""
    f = open(input_name, "r")
    contents = f.read()
    parsed = loads(contents)
    funcs = []
    aux_dict = {}
    # TODO: find a more elegant solution
    for definition in parsed[1:]:
        cur_func = load_function(definition, avail_aux=aux_dict)
        funcs.append(cur_func)
        aux_dict[cur_func.name] = cur_func
    print_all(output_name, funcs)


def read_functions(func_list: List[Union[List[Any], Symbol, str]]) -> List[str]:
    """Construct a list of function names from the parsed S-expression
    <func_list> representing a list of functions.
    Format of <func_list>:
    ["functions", [<function_list>]]
    """
    return [func_symbol.value for func_symbol in func_list[1]]


def load_function(func_exp: List[Union[List[Any], Symbol, str]],
                  avail_aux: Dict[str, Function]) -> Function:
    """Construct a Dafny Function from the parsed S-expression <func_exp>
    representing the function definition. <avail_aux> is a dictionary
    {name: function} of functions already defined.
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
    name = func_exp[1].value()
    param_types = [eval(_type.value()) for _type in func_exp[2][1]]
    param_names = [param.value() for param in func_exp[3][1][1]]
    return_type = Type([Type([], eval(func_exp[2][2].value()))])
    decreases = [dec.value() for dec in func_exp[5][1]]
    requires = func_exp[6][1]
    ensures = func_exp[7][1]
    aux_names = [symbol.value() for symbol in func_exp[8][1]]
    aux = []
    for cur in aux_names:
        try:
            aux.append(avail_aux[cur])
        except KeyError:
            print(f"Function {cur} has not been defined.")
    body = func_exp[3][1][2]
    join_body = func_exp[4][1][2]
    return Function(name, param_names, param_types, return_type,
                    decreases, requires, ensures, aux, body, join_body)

