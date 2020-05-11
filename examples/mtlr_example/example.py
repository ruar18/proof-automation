"""Example, with 5 main functions:
    - recSumS
    - Mrr
    - Mcr
    - Mtlr
    - Mblr
"""

from dafny import *
import program_loader

seq_2d = Type([], Dafny.SEQ2D)
seq_simple = Type([], Dafny.SEQ)
_int_simple = Type([], Dafny.INT)

# seq_2d = Type([seq_2d_simple])  # keep seq_2d simple
seq = Type([seq_simple])
_int = Type([_int_simple])

####### recSumS definition #######
rec_sum_body = """if s == [] then [] else if |s| == 1 then preSum(s[0]) else  
    vAdd(recSumS(s[..|s|-1]), preSum(s[|s|-1]))"""
rec_sum_join = """vAdd(a, b)"""

rec_sum = Function("recSumS", ["s"], [seq_2d], seq, [], [],
                   ["|recSumS(s)| == width(s)"], [], rec_sum_body, rec_sum_join)

####### Mrr definition #######
mrr_body = """(if s == [] then 0 else if |s| == 1 then vMax(zeroSeq(|s[|s|-1]|), 
    preSum(s[|s|-1])) else vMax(recSumS(s[..|s|-1]), preSum(s[|s|-1])))"""
mrr_join = """vMax(a.1, b.1)"""

mrr = Function("Mrr", ["s"], [seq_2d], _int, [], [], [], [rec_sum],
               mrr_body, mrr_join)

####### Mcr definition #######
mcr_body = """(if s == [] then []  else if |s| == 1 then preSum(s[0]) else 
    pMax(recSumS(s), Mcr(s[..|s|-1]).0))"""
mcr_join = """pMax(vAdd(a.1, b.0), a.0)"""

mcr = Function("Mcr", ["s"], [seq_2d], seq, [], [],
               ["|Mcr(s).0| == width(s)"], [rec_sum], mcr_body, mcr_join)

####### Mtlr definition #######
mtlr_body = """(if s == [] then 0 else Max(Mtlr(s[..|s|-1]).0, Mrr(s).0))"""
mtlr_join = """Max(a.0, vMax(a.1.1, b.1.0))"""

mtlr = Function("Mtlr", ["s"], [seq_2d], _int, [], [], [], [mcr], mtlr_body,
                mtlr_join)

####### Mblr definition #######
# Note: this Mblr computes the best bottom-left rectangle of each width
mblr_body = """(if s == [] then zeroSeq(width(s))
                else if |s| == 1 then pMax(zeroSeq(|s[|s|-1]|), preSum(s[|s|-1]))
                else pMax(vAdd(Mblr(s[..|s|-1]).0, preSum(s[|s|-1])),
                     Mblr([s[|s|-1]]).0 ))"""
mblr_join = """pMax(vAdd(a.0, b.1), b.0)"""

mblr = Function("Mblr", ["s"], [seq_2d], seq, ["|s|"], [], [], [rec_sum],
                mblr_body, mblr_join)

all_funcs = [rec_sum, mrr, mcr, mtlr, mblr]


def test_printing() -> None:
    program_loader.generate_proof("example_input.txt",
                                  "output.dfy")


if __name__ == '__main__':
    import pytest

    pytest.main(['example.py'])
