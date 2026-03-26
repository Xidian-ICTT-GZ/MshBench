class Program {
/*@
predicate array_slice(byte[] a; int from, int to, list<byte> elems) =
    from <= to &*& to <= a.length &*& a != null &*&
    array_slice(a, from, to, elems) ==
        (from == to
            ? emp &*& elems == nil
            : a[from] |-> ?v &*& array_slice(a, from + 1, to, ?tail) &*& elems == cons(v, tail));
@*/

static void rotate(byte[] xs, short start, short end)
//@ requires array_slice(xs, 0, xs.length, ?elems0) &*& 0 <= start &*& start <= end &*& end <= xs.length &*& start < end;
//@ ensures array_slice(xs, 0, xs.length, ?elems1) &*& elems1 == rotate_slice(elems0, start, end);
{
    if (start >= end - 1)
        return;
    byte last = xs[end - 1];
    //@ short loop_end = (short)(end - 1);
    //@ short i = start;
    //@ list<byte> prefix = take(start, elems0);
    //@ list<byte> middle = drop(start, take(end - 1, elems0));
    //@ list<byte> suffix = drop(end - 1, elems0);
    //@ close array_slice(xs, 0, start, prefix);
    //@ close array_slice(xs, start, end - 1, middle);
    //@ close array_slice(xs, end - 1, end, cons(last, nil));
    //@ close array_slice(xs, end, xs.length, suffix);
    for (short i = start; i < end - 1; i++)
    //@ invariant array_slice(xs, 0, start, prefix) &*& array_slice(xs, start, i, ?loop_middle) &*& xs[i] |-> ?current_val &*& array_slice(xs, i + 1, end - 1, ?loop_rest) &*& array_slice(xs, end - 1, end, cons(last, nil)) &*& array_slice(xs, end, xs.length, suffix) &*& loop_middle == take(i - start, middle) &*& cons(current_val, loop_rest) == drop(i - start, middle);
    {
        xs[i + 1] = xs[i];
        //@ open array_slice(xs, i + 1, end - 1, loop_rest);
        //@ close array_slice(xs, i + 1, end - 1, loop_rest);
    }
    xs[start] = last;
    //@ open array_slice(xs, 0, start, prefix);
    //@ open array_slice(xs, start, end - 1, middle);
    //@ open array_slice(xs, end - 1, end, cons(last, nil));
    //@ open array_slice(xs, end, xs.length, suffix);
    //@ close array_slice(xs, 0, xs.length, append(prefix, cons(last, append(middle, suffix))));
}

/*@
fixpoint list<t> rotate_slice<t>(list<t> l, int start, int end) {
    return append(take(start, l), append(cons(nth(end - 1, l), nil), append(drop(start, take(end - 1, l)), drop(end, l))));
}
@*/
}