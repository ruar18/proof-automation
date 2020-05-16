"""Example, with 4 main functions:
    - ls
    - mbl
    - mtl
    - ml
"""

from src import program_loader


def test_printing() -> None:
    program_loader.generate_proof("example_input.txt",
                                  "output.dfy")


if __name__ == '__main__':
    import pytest

    pytest.main(['example.py'])
