"""MTLR example, with 4 main functions:
    - recSumS
    - Mrr
    - Mcr
    - Mtlr
"""

from dafny import *
import format
import string

seq_2d = Type([], Dafny.SEQ2D)
seq_simple = Type([], Dafny.SEQ)
_int_simple = Type([], Dafny.INT)

# seq_2d = Type([seq_2d_simple])  # keep seq_2d simple
seq = Type([seq_simple])
_int = Type([_int_simple])

####### recSumS definition #######
rec_sum_body = """if s == [] then [] else if |s| == 1 then preSum(s[0]) else  
    vAdd(recSumS(s[..|s|-1]), preSum(s[|s|-1]))"""
rec_sum_join = """vAdd(a,b)"""

rec_sum = Function("recSumS", ["s"], [seq_2d], seq, [],
                   ["|recSumS(s)| == width(s)"], [], rec_sum_body, rec_sum_join)

####### Mrr definition #######
mrr_body = """(if s == [] then 0 else if |s| == 1 then vMax(zeroSeq(|s[|s|-1]|), 
    preSum(s[|s|-1])) else vMax(recSumS(s[..|s|-1]), preSum(s[|s|-1])))"""
mrr_join = """vMax(a.1, b.1)"""

mrr = Function("Mrr", ["s"], [seq_2d], _int, [], [], [rec_sum],
               mrr_body, mrr_join)

####### Mcr definition #######
mcr_body = """(if s == [] then []  else if |s| == 1 then preSum(s[0]) else 
    pMax(recSumS(s), Mcr(s[..|s|-1]).0))"""
mcr_join = """pMax(vAdd(a.1, b.0), a.0)"""

mcr = Function("Mcr", ["s"], [seq_2d], seq, [],
               ["ensures |Mcr(s).0| == width(s)"], [rec_sum], mcr_body, mcr_join)

####### Mtlr definition #######
mtlr_body = """(if s == [] then 0 else Max(Mtlr(s[..|s|-1]).0, Mrr(s).0))"""
mtlr_join = """Max(a.0, vMax(a.1.1, b.1.0))"""

mtlr = Function("Mtlr", ["s"], [seq_2d], _int, [], [], [mcr], mtlr_body,
                mtlr_join)


def strip_whitespace(s: str) -> str:
    """Strips all whitespace from <s>."""
    return s.translate(str.maketrans('', '', string.whitespace))


def test_printing() -> None:
    """Temporary: print the current functions to the file."""
    f = open("output.txt", "w")
    f.write(format.pp_lifted_function(rec_sum) + "\n\n")
    f.write(format.pp_lifted_function(mrr) + "\n\n")
    f.write(format.pp_lifted_function(mcr) + "\n\n")
    f.write(format.pp_lifted_join(rec_sum) + "\n\n")
    f.write(format.pp_assoc_proof(rec_sum) + "\n\n")
    f.write(format.pp_hom_proof(rec_sum) + "\n\n")
    f.write(format.pp_lifted_function(mtlr) + "\n\n")
    f.write(format.pp_lifted_join(mtlr) + "\n\n")
    f.write(format.pp_assoc_proof(mtlr) + "\n\n")
    f.write(format.pp_hom_proof(mtlr) + "\n\n")


if __name__ == '__main__':
    import pytest

    pytest.main(['test_mtlr.py'])
