"""Example, with 4 main functions:
    - ls
    - mbl
    - mtl
    - ml
"""

from dafny import *
import proof_print
import program_loader
from sexpdata import loads
import format


def test_printing() -> None:
    program_loader.generate_proof("examples/mlr_example/example_input.txt",
                                  "examples/mlr_example/output.dfy")


if __name__ == '__main__':
    import pytest

    pytest.main(['example.py'])
