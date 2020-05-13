function ls(s: seq2D): (seq<int>)
    ensures |ls(s)| == width(s)
{
    var lsRes := (if s == [] then [] else if |s| == 1 then preSum(s[0]) else vAdd(ls(s[..|s|-1]), preSum(s[|s|-1])));
    (lsRes)
}

function mbl(s: seq2D): ((seq<int>), (seq<int>))
    decreases |s|
    ensures |mbl(s).0| == width(s)
{
    var mblRes := (if s == [] then [] else if |s| == 1 then pMax(preSum(s[0]), zeroSeq(|s[0]|))
        else pMax(mbl([s[|s|-1]]).0, vAdd(mbl(s[..|s|-1]).0, preSum(s[|s|-1]))));
    var lsRes := ls(s);
    (mblRes, lsRes)
}

function mtl(s: seq2D): ((seq<int>), (seq<int>))
    decreases |s|
    ensures |mtl(s).0| == width(s)
{
    var mtlRes := (if s == [] then [] else if |s| == 1 then pMax(preSum(s[0]), zeroSeq(|s[0]|))
        else pMax(mtl(s[..|s|-1]).0, vAdd(mtl([s[|s|-1]]).0, ls(s[..|s|-1]))));
    var lsRes := ls(s);
    (mtlRes, lsRes)
}

function ml(s: seq2D): ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>)))
    decreases |s|
    ensures |ml(s).0| == width(s)
{
    var mlRes := (if s == [] then [] else if |s| == 1 then pMax(preSum(s[0]), zeroSeq(|s[0]|))
                                else pMax(pMax(ml(s[..|s|-1]).0, ml([s[|s|-1]]).0), vAdd(mbl(s[..|s|-1]).0, mtl([s[|s|-1]]).0)));
    var mblRes := mbl(s);
    var mtlRes := mtl(s);
    (mlRes, mblRes, mtlRes)
}

function lsJoin(a: (seq<int>), b: (seq<int>)): (seq<int>)
    requires |a| == |b|
{
    var lsRes := (vAdd(a, b));
    (lsRes)
}

function mblJoin(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>))): ((seq<int>), (seq<int>))
    requires |a.0| == |a.1| == |b.0| == |b.1|
{
    var mblRes := (pMax(b.0, vAdd(a.0, b.1)));
    var lsRes := lsJoin(a.1, b.1);
    (mblRes, lsRes)
}

function mtlJoin(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>))): ((seq<int>), (seq<int>))
    requires |a.0| == |a.1| == |b.0| == |b.1|
{
    var mtlRes := (pMax(a.0, vAdd(b.0, a.1)));
    var lsRes := lsJoin(a.1, b.1);
    (mtlRes, lsRes)
}

function mlJoin(a: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))), b: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>)))): ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>)))
    requires |a.0| == |a.1.0| == |a.1.1| == |a.2.0| == |a.2.1| == |b.0| == |b.1.0| == |b.1.1| == |b.2.0| == |b.2.1|
{
    var mlRes := (pMax(pMax(a.0, b.0), vAdd(a.1.0, b.2.0)));
    var mblRes := mblJoin(a.1, b.1);
    var mtlRes := mtlJoin(a.2, b.2);
    (mlRes, mblRes, mtlRes)
}

lemma lsJoinAssoc(a: (seq<int>), b: (seq<int>), c: (seq<int>))
    decreases |a|, |b|, |c|
    requires |a| == |b| == |c| 
    ensures lsJoin(lsJoin(a, b), c) == lsJoin(a, lsJoin(b, c))
{
    if |a| == 0 {}
    else if |a| == 1 {}
    else
    {
        var a' := a[..|a|-1];
        var b' := b[..|b|-1];
        var c' := c[..|c|-1];
        lsJoinAssoc((a'), (b'), (c'));

        var af := [a[|a|-1]];
        var bf := [b[|b|-1]];
        var cf := [c[|c|-1]];
        lsJoinAssoc((af), (bf), (cf));
    }
}

lemma mblJoinAssoc(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>)), c: ((seq<int>), (seq<int>)))
    decreases |a.0|, |a.1|, |b.0|, |b.1|, |c.0|, |c.1|
    requires |a.0| == |a.1| == |b.0| == |b.1| == |c.0| == |c.1| 
    ensures mblJoin(mblJoin(a, b), c) == mblJoin(a, mblJoin(b, c))
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
        mblJoinAssoc(((a0', a1')), ((b0', b1')), ((c0', c1')));

        var a0f := [a.0[|a.0|-1]];
        var a1f := [a.1[|a.1|-1]];
        var b0f := [b.0[|b.0|-1]];
        var b1f := [b.1[|b.1|-1]];
        var c0f := [c.0[|c.0|-1]];
        var c1f := [c.1[|c.1|-1]];
        mblJoinAssoc(((a0f, a1f)), ((b0f, b1f)), ((c0f, c1f)));
    }
}

lemma mtlJoinAssoc(a: ((seq<int>), (seq<int>)), b: ((seq<int>), (seq<int>)), c: ((seq<int>), (seq<int>)))
    decreases |a.0|, |a.1|, |b.0|, |b.1|, |c.0|, |c.1|
    requires |a.0| == |a.1| == |b.0| == |b.1| == |c.0| == |c.1| 
    ensures mtlJoin(mtlJoin(a, b), c) == mtlJoin(a, mtlJoin(b, c))
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
        mtlJoinAssoc(((a0', a1')), ((b0', b1')), ((c0', c1')));

        var a0f := [a.0[|a.0|-1]];
        var a1f := [a.1[|a.1|-1]];
        var b0f := [b.0[|b.0|-1]];
        var b1f := [b.1[|b.1|-1]];
        var c0f := [c.0[|c.0|-1]];
        var c1f := [c.1[|c.1|-1]];
        mtlJoinAssoc(((a0f, a1f)), ((b0f, b1f)), ((c0f, c1f)));
    }
}

lemma mlJoinAssoc(a: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))), b: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))), c: ((seq<int>), ((seq<int>), (seq<int>)), ((seq<int>), (seq<int>))))
    decreases |a.0|, |a.1.0|, |a.1.1|, |a.2.0|, |a.2.1|, |b.0|, |b.1.0|, |b.1.1|, |b.2.0|, |b.2.1|, |c.0|, |c.1.0|, |c.1.1|, |c.2.0|, |c.2.1|
    requires |a.0| == |a.1.0| == |a.1.1| == |a.2.0| == |a.2.1| == |b.0| == |b.1.0| == |b.1.1| == |b.2.0| == |b.2.1| == |c.0| == |c.1.0| == |c.1.1| == |c.2.0| == |c.2.1|  && a.1.1 == a.2.1 && b.1.1 == b.2.1 && c.1.1 == c.2.1
    ensures mlJoin(mlJoin(a, b), c) == mlJoin(a, mlJoin(b, c))
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
        mlJoinAssoc(((a0', (a10', a11'), (a20', a21'))), ((b0', (b10', b11'), (b20', b21'))), ((c0', (c10', c11'), (c20', c21'))));

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
        mlJoinAssoc(((a0f, (a10f, a11f), (a20f, a21f))), ((b0f, (b10f, b11f), (b20f, b21f))), ((c0f, (c10f, c11f), (c20f, c21f))));
    }
}

lemma Homls(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures ls(s + t) == lsJoin(ls(s), ls(t))
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
        Homls(s, t1);
        lsJoinAssoc(ls(s), ls(t1), ls(t2));
    }
}

lemma Hommbl(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures mbl(s + t) == mblJoin(mbl(s), mbl(t))
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
        Hommbl(s, t1);
        mblJoinAssoc(mbl(s), mbl(t1), mbl(t2));
    }
}

lemma Hommtl(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures mtl(s + t) == mtlJoin(mtl(s), mtl(t))
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
        Hommtl(s, t1);
        mtlJoinAssoc(mtl(s), mtl(t1), mtl(t2));
    }
}

lemma Homml(s: seq2D, t: seq2D)
    requires width(s) == width(t)
    ensures ml(s + t) == mlJoin(ml(s), ml(t))
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
        Homml(s, t1);
        mlJoinAssoc(ml(s), ml(t1), ml(t2));
    }
}

