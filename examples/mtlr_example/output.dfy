function recSumS(s: seq2D): seq<int>
    ensures |recSumS(s)| == width(s)
{
    var recSumSRes := if s == [] then [] else if |s| == 1 then preSum(s[0]) else vAdd(recSumS(s[..|s|-1]), preSum(s[|s|-1]));
    (recSumSRes)
}

function Mrr(s: seq2D): (int, seq<int>)
{
    var MrrRes := if s == [] then 0 else if |s| == 1 then vMax(zeroSeq(|s[|s|-1]|), preSum(s[|s|-1])) else vMax(recSumS(s[..|s|-1]), preSum(s[|s|-1]));
    var recSumSRes := recSumS(s);
    (MrrRes, recSumSRes)
}

function Mcr(s: seq2D): (seq<int>, seq<int>)
    ensures |Mcr(s).0| == width(s)
{
    var McrRes := if s == [] then []  else if |s| == 1 then preSum(s[0]) else pMax(recSumS(s), Mcr(s[..|s|-1]).0);
    var recSumSRes := recSumS(s);
    (McrRes, recSumSRes)
}

function Mtlr(s: seq2D): (int, (seq<int>, seq<int>))
{
    var MtlrRes := (if s == [] then 0 else Max(Mtlr(s[..|s|-1]).0, Mrr(s).0));
    var McrRes := Mcr(s);
    (MtlrRes, McrRes)
}

function Mblr(s: seq2D): (seq<int>, seq<int>)
    decreases |s|
{
    var MblrRes := if s == [] then zeroSeq(width(s))
                    else if |s| == 1 then pMax(zeroSeq(|s[|s|-1]|), preSum(s[|s|-1]))
                    else pMax(vAdd(Mblr(s[..|s|-1]).0, preSum(s[|s|-1])),
                         Mblr([s[|s|-1]]).0);
    var recSumSRes := recSumS(s);
    (MblrRes, recSumSRes)
}

function recSumSJoin(a: seq<int>, b: seq<int>): seq<int>
    requires |a| == |b|
{
    var recSumSRes := vAdd(a, b);
    (recSumSRes)
}

function MrrJoin(a: (int, seq<int>), b: (int, seq<int>)): (int, seq<int>)
    requires |a.1| == |b.1|
{
    var MrrRes := vMax(a.1, b.1);
    var recSumSRes := recSumSJoin(a.1, b.1);
    (MrrRes, recSumSRes)
}

function McrJoin(a: (seq<int>, seq<int>), b: (seq<int>, seq<int>)): (seq<int>, seq<int>)
    requires |a.0| == |a.1| == |b.0| == |b.1|
{
    var McrRes := pMax(vAdd(a.1, b.0), a.0);
    var recSumSRes := recSumSJoin(a.1, b.1);
    (McrRes, recSumSRes)
}

function MtlrJoin(a: (int, (seq<int>, seq<int>)), b: (int, (seq<int>, seq<int>))): (int, (seq<int>, seq<int>))
    requires |a.1.0| == |a.1.1| == |b.1.0| == |b.1.1|
{
    var MtlrRes := Max(a.0, vMax(a.1.1, b.1.0));
    var McrRes := McrJoin(a.1, b.1);
    (MtlrRes, McrRes)
}

function MblrJoin(a: (seq<int>, seq<int>), b: (seq<int>, seq<int>)): (seq<int>, seq<int>)
    requires |a.0| == |a.1| == |b.0| == |b.1|
{
    var MblrRes := pMax(vAdd(a.0, b.1), b.0);
    var recSumSRes := recSumSJoin(a.1, b.1);
    (MblrRes, recSumSRes)
}

lemma recSumSJoinAssoc(a: seq<int>, b: seq<int>, c: seq<int>)
    decreases |a|, |b|, |c|
    requires |a| == |b| == |c| 
    ensures recSumSJoin(recSumSJoin(a, b), c) == recSumSJoin(a, recSumSJoin(b, c))
{
    var n := |a|;
    if n == 0 {}
    else if n == 1 {}
    else
    {
        var a' := a[..n-1];
        var b' := b[..n-1];
        var c' := c[..n-1];
        recSumSJoinAssoc((a'), (b'), (c'));

        var af := [a[n-1]];
        var bf := [b[n-1]];
        var cf := [c[n-1]];
        recSumSJoinAssoc((af), (bf), (cf));
    }
}

lemma MrrJoinAssoc(a: (int, seq<int>), b: (int, seq<int>), c: (int, seq<int>))
    decreases |a.1|, |b.1|, |c.1|
    requires |a.1| == |b.1| == |c.1| 
    ensures MrrJoin(MrrJoin(a, b), c) == MrrJoin(a, MrrJoin(b, c))
{
    var n := |a.1|;
    if n == 0 {}
    else if n == 1 {}
    else
    {
        var a1' := a.1[..n-1];
        var b1' := b.1[..n-1];
        var c1' := c.1[..n-1];
        MrrJoinAssoc((((a.0), a1')), (((b.0), b1')), (((c.0), c1')));

        var a1f := [a.1[n-1]];
        var b1f := [b.1[n-1]];
        var c1f := [c.1[n-1]];
        MrrJoinAssoc((((a.0), a1f)), (((b.0), b1f)), (((c.0), c1f)));
    }
}

lemma McrJoinAssoc(a: (seq<int>, seq<int>), b: (seq<int>, seq<int>), c: (seq<int>, seq<int>))
    decreases |a.0|, |a.1|, |b.0|, |b.1|, |c.0|, |c.1|
    requires |a.0| == |a.1| == |b.0| == |b.1| == |c.0| == |c.1| 
    ensures McrJoin(McrJoin(a, b), c) == McrJoin(a, McrJoin(b, c))
{
    var n := |a.0|;
    if n == 0 {}
    else if n == 1 {}
    else
    {
        var a0' := a.0[..n-1];
        var a1' := a.1[..n-1];
        var b0' := b.0[..n-1];
        var b1' := b.1[..n-1];
        var c0' := c.0[..n-1];
        var c1' := c.1[..n-1];
        McrJoinAssoc(((a0', a1')), ((b0', b1')), ((c0', c1')));

        var a0f := [a.0[n-1]];
        var a1f := [a.1[n-1]];
        var b0f := [b.0[n-1]];
        var b1f := [b.1[n-1]];
        var c0f := [c.0[n-1]];
        var c1f := [c.1[n-1]];
        McrJoinAssoc(((a0f, a1f)), ((b0f, b1f)), ((c0f, c1f)));
    }
}

lemma MtlrJoinAssoc(a: (int, (seq<int>, seq<int>)), b: (int, (seq<int>, seq<int>)), c: (int, (seq<int>, seq<int>)))
    decreases |a.1.0|, |a.1.1|, |b.1.0|, |b.1.1|, |c.1.0|, |c.1.1|
    requires |a.1.0| == |a.1.1| == |b.1.0| == |b.1.1| == |c.1.0| == |c.1.1| 
    ensures MtlrJoin(MtlrJoin(a, b), c) == MtlrJoin(a, MtlrJoin(b, c))
{
    var n := |a.1.0|;
    if n == 0 {}
    else if n == 1 {}
    else
    {
        var a10' := a.1.0[..n-1];
        var a11' := a.1.1[..n-1];
        var b10' := b.1.0[..n-1];
        var b11' := b.1.1[..n-1];
        var c10' := c.1.0[..n-1];
        var c11' := c.1.1[..n-1];
        MtlrJoinAssoc((((a.0), (a10', a11'))), (((b.0), (b10', b11'))), (((c.0), (c10', c11'))));

        var a10f := [a.1.0[n-1]];
        var a11f := [a.1.1[n-1]];
        var b10f := [b.1.0[n-1]];
        var b11f := [b.1.1[n-1]];
        var c10f := [c.1.0[n-1]];
        var c11f := [c.1.1[n-1]];
        MtlrJoinAssoc((((a.0), (a10f, a11f))), (((b.0), (b10f, b11f))), (((c.0), (c10f, c11f))));
    }
}

lemma MblrJoinAssoc(a: (seq<int>, seq<int>), b: (seq<int>, seq<int>), c: (seq<int>, seq<int>))
    decreases |a.0|, |a.1|, |b.0|, |b.1|, |c.0|, |c.1|
    requires |a.0| == |a.1| == |b.0| == |b.1| == |c.0| == |c.1| 
    ensures MblrJoin(MblrJoin(a, b), c) == MblrJoin(a, MblrJoin(b, c))
{
    var n := |a.0|;
    if n == 0 {}
    else if n == 1 {}
    else
    {
        var a0' := a.0[..n-1];
        var a1' := a.1[..n-1];
        var b0' := b.0[..n-1];
        var b1' := b.1[..n-1];
        var c0' := c.0[..n-1];
        var c1' := c.1[..n-1];
        MblrJoinAssoc(((a0', a1')), ((b0', b1')), ((c0', c1')));

        var a0f := [a.0[n-1]];
        var a1f := [a.1[n-1]];
        var b0f := [b.0[n-1]];
        var b1f := [b.1[n-1]];
        var c0f := [c.0[n-1]];
        var c1f := [c.1[n-1]];
        MblrJoinAssoc(((a0f, a1f)), ((b0f, b1f)), ((c0f, c1f)));
    }
}

lemma HomrecSumS(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures recSumS(s + t) == recSumSJoin(recSumS(s), recSumS(t))
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
        HomrecSumS(s, t1);
        recSumSJoinAssoc(recSumS(s), recSumS(t1), recSumS(t2));
    }
}

lemma HomMrr(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Mrr(s + t) == MrrJoin(Mrr(s), Mrr(t))
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
        HomMrr(s, t1);
        MrrJoinAssoc(Mrr(s), Mrr(t1), Mrr(t2));
    }
}

lemma HomMcr(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Mcr(s + t) == McrJoin(Mcr(s), Mcr(t))
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
        HomMcr(s, t1);
        McrJoinAssoc(Mcr(s), Mcr(t1), Mcr(t2));
    }
}

lemma HomMtlr(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Mtlr(s + t) == MtlrJoin(Mtlr(s), Mtlr(t))
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
        HomMtlr(s, t1);
        MtlrJoinAssoc(Mtlr(s), Mtlr(t1), Mtlr(t2));
    }
}

lemma HomMblr(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures Mblr(s + t) == MblrJoin(Mblr(s), Mblr(t))
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
        HomMblr(s, t1);
        MblrJoinAssoc(Mblr(s), Mblr(t1), Mblr(t2));
    }
}

