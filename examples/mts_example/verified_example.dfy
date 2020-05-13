// Full example (with auxiliary function definitions) that verifies.
function Max(x: int, y: int): (int)
{
  (if x < y then y else x)
}

// Code below is generated automatically
function Sum(s: seq<int>): (int)
{
    var SumRes := (if s == [] then 0 else Sum(s[..|s|-1]) + s[|s|-1]);
    (SumRes)
}

function Mts(s: seq<int>): ((int), (int))
{
    var MtsRes := (if s == [] then 0 else Max(Mts(s[..|s|-1]).0 + s[|s|-1], 0));
    var SumRes := Sum(s);
    (MtsRes, SumRes)
}

function SumJoin(a: (int), b: (int)): (int)
{
    var SumRes := (a + b);
    (SumRes)
}

function MtsJoin(a: ((int), (int)), b: ((int), (int))): ((int), (int))
{
    var MtsRes := (Max(b.0, a.0 + b.1));
    var SumRes := SumJoin(a.1, b.1);
    (MtsRes, SumRes)
}

lemma SumJoinAssoc(a: (int), b: (int), c: (int))
    ensures SumJoin(SumJoin(a, b), c) == SumJoin(a, SumJoin(b, c))
{
}

lemma MtsJoinAssoc(a: ((int), (int)), b: ((int), (int)), c: ((int), (int)))
    ensures MtsJoin(MtsJoin(a, b), c) == MtsJoin(a, MtsJoin(b, c))
{
}

lemma HomSum(s: seq<int>, t: seq<int>)
    ensures Sum(s + t) == SumJoin(Sum(s), Sum(t))
{
    if t == []
    {
        assert s + t == s;
    }
    else if |t| == 1
    {
    }
    else
    {
        var t1 := t[..|t|-1];
        var t2 := [t[|t|-1]];
        assert (s + t1) + t2 == s + t;
        HomSum(s, t1);
        SumJoinAssoc(Sum(s), Sum(t1), Sum(t2));
    }
}

lemma HomMts(s: seq<int>, t: seq<int>)
    ensures Mts(s + t) == MtsJoin(Mts(s), Mts(t))
{
    if t == []
    {
        assert s + t == s;
    }
    else if |t| == 1
    {
    }
    else
    {
        var t1 := t[..|t|-1];
        var t2 := [t[|t|-1]];
        assert (s + t1) + t2 == s + t;
        HomMts(s, t1);
        MtsJoinAssoc(Mts(s), Mts(t1), Mts(t2));
    }
}