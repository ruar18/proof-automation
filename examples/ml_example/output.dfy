function Ls(s: seq2D): (seq<int>)
    ensures |Ls(s)| == width(s)
{
    var LsRes := (if s == [] then [] else if |s| == 1 then preSum(s[0]) else vAdd(Ls(s[..|s|-1]), preSum(s[|s|-1])));
    (LsRes)
}

function Mbl(s: seq2D): ((seq<int>), (seq<int>))
    decreases |s|
    ensures |Mbl(s).0| == width(s)
{
    var MblRes := (if s == [] then [] else if |s| == 1 then pMax(preSum(s[0]), zeroSeq(|s[0]|))
        else pMax(Mbl([s[|s|-1]]).0, vAdd(Mbl(s[..|s|-1]).0, preSum(s[|s|-1]))));
    var LsRes := Ls(s);
    (MblRes, LsRes)
}

function Mtl(s: seq2D): ((seq<int>), (seq<int>))
    decreases |s|
    ensures |Mtl(s).0| == width(s)
{
    var MtlRes := (if s == [] then [] else if |s| == 1 then pMax(preSum(s[0]), zeroSeq(|s[0]|))
        else pMax(Mtl(s[..|s|-1]).0, vAdd(Mtl([s[|s|-1]]).0, Ls(s[..|s|-1]))));
    var LsRes := Ls(s);
    (MtlRes, LsRes)
}

function Ml(s: seq2D): ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>)))
    decreases |s|
    ensures |Ml(s).0| == width(s)
{
    var MlRes := (if s == [] then [] else if |s| == 1 then pMax(preSum(s[0]), zeroSeq(|s[0]|))
                                else pMax(pMax(Ml(s[..|s|-1]).0, Ml([s[|s|-1]]).0), vAdd(Mbl(s[..|s|-1]).0, Mtl([s[|s|-1]]).0)));
    var MblRes := Mbl(s);
    var MtlRes := Mtl(s);
    (MlRes, MblRes, MtlRes)
}

function LsJoin(a: (seq<int>), b: (seq<int>)): (seq<int>)
    requires |a| == |b|
{
    var LsRes := (vAdd(a, b));
    (LsRes)
}

function MblJoin(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>))): ((seq<int>), (seq<int>))
    requires |a.0| == |a.1| == |b.0| == |b.1|
{
    var MblRes := (pMax(b.0, vAdd(a.0, b.1)));
    var LsRes := LsJoin(a.1, b.1);
    (MblRes, LsRes)
}

function MtlJoin(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>))): ((seq<int>), (seq<int>))
    requires |a.0| == |a.1| == |b.0| == |b.1|
{
    var MtlRes := (pMax(a.0, vAdd(b.0, a.1)));
    var LsRes := LsJoin(a.1, b.1);
    (MtlRes, LsRes)
}

function MlJoin(a: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))), b: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>)))): ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>)))
    requires |a.0| == |a.1.0| == |a.1.1| == |a.2.0| == |a.2.1| == |b.0| == |b.1.0| == |b.1.1| == |b.2.0| == |b.2.1|
{
    var MlRes := (pMax(pMax(a.0, b.0), vAdd(a.1.0, b.2.0)));
    var MblRes := MblJoin(a.1, b.1);
    var MtlRes := MtlJoin(a.2, b.2);
    (MlRes, MblRes, MtlRes)
}

lemma LsJoinAssoc(a: (seq<int>), b: (seq<int>), c: (seq<int>))
    decreases |a|, |b|, |c|
    requires |a| == |b| == |c| 
    ensures LsJoin(LsJoin(a, b), c) == LsJoin(a, LsJoin(b, c))
{
    if |a| == 0 {}
    else if |a| == 1 {}
    else
    {
        var a' := a[..|a|-1];
        var b' := b[..|b|-1];
        var c' := c[..|c|-1];
        LsJoinAssoc((a'), (b'), (c'));

        var af := [a[|a|-1]];
        var bf := [b[|b|-1]];
        var cf := [c[|c|-1]];
        LsJoinAssoc((af), (bf), (cf));
    }
}

lemma MblJoinAssoc(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>)), c: ((seq<int>), (seq<int>)))
    decreases |a.0|, |a.1|, |b.0|, |b.1|, |c.0|, |c.1|
    requires |a.0| == |a.1| == |b.0| == |b.1| == |c.0| == |c.1| 
    ensures MblJoin(MblJoin(a, b), c) == MblJoin(a, MblJoin(b, c))
{
    if |a.0| == 0 {}
    else if |a.0| == 1 {}
    else
    {
        var a0' := a.0[..|a.0|-1];
        var a1' := a.1[..|a.1|-1];
        var b0' := b.0[..|b.0|-1];
        var b1' := b.1[..|b.1|-1];
        var c0' := c.0[..|c.0|-1];
        var c1' := c.1[..|c.1|-1];
        MblJoinAssoc(((a0', a1')), ((b0', b1')), ((c0', c1')));

        var a0f := [a.0[|a.0|-1]];
        var a1f := [a.1[|a.1|-1]];
        var b0f := [b.0[|b.0|-1]];
        var b1f := [b.1[|b.1|-1]];
        var c0f := [c.0[|c.0|-1]];
        var c1f := [c.1[|c.1|-1]];
        MblJoinAssoc(((a0f, a1f)), ((b0f, b1f)), ((c0f, c1f)));
    }
}

lemma MtlJoinAssoc(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>)), c: ((seq<int>), (seq<int>)))
    decreases |a.0|, |a.1|, |b.0|, |b.1|, |c.0|, |c.1|
    requires |a.0| == |a.1| == |b.0| == |b.1| == |c.0| == |c.1| 
    ensures MtlJoin(MtlJoin(a, b), c) == MtlJoin(a, MtlJoin(b, c))
{
    if |a.0| == 0 {}
    else if |a.0| == 1 {}
    else
    {
        var a0' := a.0[..|a.0|-1];
        var a1' := a.1[..|a.1|-1];
        var b0' := b.0[..|b.0|-1];
        var b1' := b.1[..|b.1|-1];
        var c0' := c.0[..|c.0|-1];
        var c1' := c.1[..|c.1|-1];
        MtlJoinAssoc(((a0', a1')), ((b0', b1')), ((c0', c1')));

        var a0f := [a.0[|a.0|-1]];
        var a1f := [a.1[|a.1|-1]];
        var b0f := [b.0[|b.0|-1]];
        var b1f := [b.1[|b.1|-1]];
        var c0f := [c.0[|c.0|-1]];
        var c1f := [c.1[|c.1|-1]];
        MtlJoinAssoc(((a0f, a1f)), ((b0f, b1f)), ((c0f, c1f)));
    }
}

lemma MlJoinAssoc(a: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))), b: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))), c: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))))
    decreases |a.0|, |a.1.0|, |a.1.1|, |a.2.0|, |a.2.1|, |b.0|, |b.1.0|, |b.1.1|, |b.2.0|, |b.2.1|, |c.0|, |c.1.0|, |c.1.1|, |c.2.0|, |c.2.1|
    requires |a.0| == |a.1.0| == |a.1.1| == |a.2.0| == |a.2.1| == |b.0| == |b.1.0| == |b.1.1| == |b.2.0| == |b.2.1| == |c.0| == |c.1.0| == |c.1.1| == |c.2.0| == |c.2.1|  && a.1.1 == a.2.1 && b.1.1 == b.2.1 && c.1.1 == c.2.1
    ensures MlJoin(MlJoin(a, b), c) == MlJoin(a, MlJoin(b, c))
{
    if |a.0| == 0 {}
    else if |a.0| == 1 {}
    else
    {
        var a0' := a.0[..|a.0|-1];
        var a10' := a.1.0[..|a.1.0|-1];
        var a11' := a.1.1[..|a.1.1|-1];
        var a20' := a.2.0[..|a.2.0|-1];
        var a21' := a.2.1[..|a.2.1|-1];
        var b0' := b.0[..|b.0|-1];
        var b10' := b.1.0[..|b.1.0|-1];
        var b11' := b.1.1[..|b.1.1|-1];
        var b20' := b.2.0[..|b.2.0|-1];
        var b21' := b.2.1[..|b.2.1|-1];
        var c0' := c.0[..|c.0|-1];
        var c10' := c.1.0[..|c.1.0|-1];
        var c11' := c.1.1[..|c.1.1|-1];
        var c20' := c.2.0[..|c.2.0|-1];
        var c21' := c.2.1[..|c.2.1|-1];
        MlJoinAssoc(((a0', (a10', a11'), (a20', a21'))), ((b0', (b10', b11'), (b20', b21'))), ((c0', (c10', c11'), (c20', c21'))));

        var a0f := [a.0[|a.0|-1]];
        var a10f := [a.1.0[|a.1.0|-1]];
        var a11f := [a.1.1[|a.1.1|-1]];
        var a20f := [a.2.0[|a.2.0|-1]];
        var a21f := [a.2.1[|a.2.1|-1]];
        var b0f := [b.0[|b.0|-1]];
        var b10f := [b.1.0[|b.1.0|-1]];
        var b11f := [b.1.1[|b.1.1|-1]];
        var b20f := [b.2.0[|b.2.0|-1]];
        var b21f := [b.2.1[|b.2.1|-1]];
        var c0f := [c.0[|c.0|-1]];
        var c10f := [c.1.0[|c.1.0|-1]];
        var c11f := [c.1.1[|c.1.1|-1]];
        var c20f := [c.2.0[|c.2.0|-1]];
        var c21f := [c.2.1[|c.2.1|-1]];
        MlJoinAssoc(((a0f, (a10f, a11f), (a20f, a21f))), ((b0f, (b10f, b11f), (b20f, b21f))), ((c0f, (c10f, c11f), (c20f, c21f))));
    }
}

lemma HomLs(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Ls(s + t) == LsJoin(Ls(s), Ls(t))
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
        HomLs(s, t1);
        LsJoinAssoc(Ls(s), Ls(t1), Ls(t2));
    }
}

lemma HomMbl(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Mbl(s + t) == MblJoin(Mbl(s), Mbl(t))
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
        HomMbl(s, t1);
        MblJoinAssoc(Mbl(s), Mbl(t1), Mbl(t2));
    }
}

lemma HomMtl(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Mtl(s + t) == MtlJoin(Mtl(s), Mtl(t))
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
        HomMtl(s, t1);
        MtlJoinAssoc(Mtl(s), Mtl(t1), Mtl(t2));
    }
}

lemma HomMl(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Ml(s + t) == MlJoin(Ml(s), Ml(t))
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
        HomMl(s, t1);
        MlJoinAssoc(Ml(s), Ml(t1), Ml(t2));
    }
}

