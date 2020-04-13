from dafny import *
import format
import string

seq_2d = Type([], Dafny.SEQ2D)
seq = Type([], Dafny.SEQ)
_int = Type([], Dafny.INT)
rec_sum_body = """if s == [] then [] else if |s| == 1 then preSum(s[0]) else  
    vAdd(recSumS(s[..|s|-1]), preSum(s[|s|-1]))"""
rec_sum_join = """vAdd(a,b)"""

rec_sum = Function("recSumS", ["s"], [seq_2d], seq, [],
                   ["|recSumS(s)| == width(s)"], [], rec_sum_body, rec_sum_join)

mrr_body = """(if s == [] then 0 else if |s| == 1 then vMax(zeroSeq(|s[|s|-1]|), 
    preSum(s[|s|-1])) else vMax(recSumS(s[..|s|-1]), preSum(s[|s|-1])))"""
mrr_join = """vMax(a.1, b.1)"""

mrr = Function("Mrr", ["s"], [seq_2d], _int, [], [], [rec_sum],
               mrr_body, mrr_join)


def strip_whitespace(s: str) -> str:
    """Strips all whitespace from <s>."""
    return s.translate(str.maketrans('', '', string.whitespace))


def test_printing() -> None:
    """Temporary: print the current functions to the file."""
    f = open("output.txt", "w")
    f.write(format.pp_lifted_function(rec_sum))
    f.write(format.pp_lifted_function(mrr))




if __name__ == '__main__':
    import pytest

    pytest.main(['test_mtlr.py'])
