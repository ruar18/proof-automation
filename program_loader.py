"""
Load a Dafny program from S-expressions representing the program.
"""
from typing import List, Union, Optional, Any
from dafny import Function, Type
from sexpdata import Symbol, loads


def load_function(func_exp: List[Union[List[Any], Symbol, str]]) -> Function:
    """Construct a Dafny Function from the parsed S-expression <func_exp>
    representing the function definition.
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
    param_types = func_exp[2][1]
    param_names = func_exp[3][1][1]
    return_type = Type([], func_exp[2][2])
    decreases = func_exp[5][1]
    requires = func_exp[6][1]
    ensures = func_exp[7][1]
    aux = func_exp[8][1]
    body = func_exp[3][1][2]
    join_body = func_exp[4][1][2]
    return Function(name, param_names, param_types, return_type,
                    decreases, requires, ensures, aux, body, join_body)

