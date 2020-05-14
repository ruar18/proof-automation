"""Example, with 5 main functions:
    - recSumS
    - Mrr
    - Mcr
    - Mtlr
    - Mblr
"""

import program_loader


def test_printing() -> None:
    program_loader.generate_proof("example_input.txt",
                                  "output.dfy")


if __name__ == '__main__':
    import pytest

    pytest.main(['example.py'])
