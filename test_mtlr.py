from dafny import *
import format

seq_2d = Type([], Dafny.SEQ2D)
seq = Type([], Dafny.SEQ)
rec_sum_body = """if s == [] then [] else if |s| == 1 then preSum(s[0]) else  
    vAdd(recSumS(s[..|s|-1]), preSum(s[|s|-1]))"""
rec_sum_join = """vAdd(a,b)"""

rec_sum = Function("recSumS", ["s"], [seq_2d], seq, [],
                   ["|recSumS(s)| == width(s)"], [], rec_sum_body, rec_sum_join)

def test_rec_sum_pp() -> None:
    print(format.pp_lifted_function(rec_sum))
    # todo: consider removing simple types and just tupling by default,
    # may make things more natural




if __name__ == '__main__':
    import pytest

    pytest.main(['test_mtlr.py'])
