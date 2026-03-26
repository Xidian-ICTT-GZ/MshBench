class Program {
    //@ predicate array_slice(byte[] a; int from, int to, list<byte> elems) = from <= to &*& to <= a.length &*& a[from..to] |-> elems;
    //@ predicate array_slice(byte[] a; int from, int to) = from <= to &*& to <= a.length &*& array_slice_char(a, from, to, _);
    //@ predicate array_slice_char(byte[] a; int from, int to, list<byte> elems) = from == to ? elems == nil : a[from] |-> ?v &*& array_slice_char(a, from + 1, to, ?tail) &*& elems == cons(v, tail);

    //@ requires xs != null;
    //@ requires 0 <= start &*& start <= end &*& end <= xs.length;
    //@ requires array_slice_char(xs, start, end, ?elems);
    //@ ensures array_slice_char(xs, start, end, ?new_elems) &*& new_elems == append(take((int)(end - start - 1), elems), cons(last_of(elems), nil));
    //@ ensures end - start <= 1 ? new_elems == elems : true;
    static void rotate(byte[] xs, short start, short end)
    {
        //@ open array_slice_char(xs, start, end, elems);
        if (start >= end - 1)
            //@ close array_slice_char(xs, start, end, elems);
            return;
        //@ short end_minus_one = (short)(end - 1);
        //@ assert end_minus_one == end - 1;
        //@ split_array_slice_char(xs, start, end_minus_one, end);
        //@ assert array_slice_char(xs, start, end_minus_one, ?prefix) &*& array_slice_char(xs, end_minus_one, end, ?suffix);
        //@ open array_slice_char(xs, end_minus_one, end, suffix);
        //@ assert xs[end_minus_one] |-> ?last;
        //@ assert suffix == cons(last, nil);
        //@ close array_slice_char(xs, end_minus_one, end, suffix);
        byte last = xs[end - 1];
        //@ short loop_end = (short)(end - 1);
        //@ short i = start;
        //@ close array_slice_char(xs, i, i, nil);
        /*@
        loop_invariant start <= i &*& i <= loop_end;
        loop_invariant array_slice_char(xs, start, i, ?written_prefix) &*& xs[i] |-> ?current &*& array_slice_char(xs, i + 1, loop_end, ?remaining) &*& array_slice_char(xs, loop_end, end, suffix);
        loop_invariant elems == append(written_prefix, cons(current, remaining));
        @*/
        for (short i = start; i < end - 1; i++)
        {
            //@ open array_slice_char(xs, i + 1, loop_end, remaining);
            //@ assert xs[i + 1] |-> ?next_val;
            xs[i + 1] = xs[i];
            //@ close array_slice_char(xs, i + 1, loop_end, cons(current, tail(remaining)));
        }
        //@ open array_slice_char(xs, loop_end, loop_end, _);
        //@ open array_slice_char(xs, loop_end, end, suffix);
        xs[start] = last;
        //@ close array_slice_char(xs, start, end, _);
    }

    //@ lemma void split_array_slice_char(byte[] a, int from, int mid, int to);
    //@ requires from <= mid &*& mid <= to &*& array_slice_char(a, from, to, ?elems);
    //@ ensures array_slice_char(a, from, mid, take(mid - from, elems)) &*& array_slice_char(a, mid, to, drop(mid - from, elems));

    //@ lemma void merge_array_slice_char(byte[] a, int from, int mid, int to);
    //@ requires from <= mid &*& mid <= to &*& array_slice_char(a, from, mid, ?elems1) &*& array_slice_char(a, mid, to, ?elems2);
    //@ ensures array_slice_char(a, from, to, append(elems1, elems2));

    //@ lemma byte last_of(list<byte> l);
    //@ requires l != nil;
    //@ ensures result == nth(length(l) - 1, l);
}