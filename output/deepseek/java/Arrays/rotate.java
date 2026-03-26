class Program {
    //@ predicate array_slice(byte[] a; int from, int to) = from >= 0 &*& from <= to &*& to <= a.length &*& array_slice_chars(a, from, to);
    //@ predicate array_slice_chars(byte[] a, int from, int to) = from >= to ? emp : chars(a, from, 1) &*& array_slice_chars(a, from + 1, to);

    //@ requires array_slice(xs, 0, xs.length);
    //@ requires 0 <= start &*& start <= end &*& end <= xs.length;
    //@ requires start < end - 1;
    //@ ensures array_slice(xs, 0, xs.length);
    static void rotate(byte[] xs, short start, short end)

    {
        //@ open array_slice(xs, 0, xs.length);
        //@ assert array_slice_chars(xs, 0, xs.length);
        //@ split_array_slice_chars(xs, 0, end, xs.length);
        //@ assert array_slice_chars(xs, 0, end);
        //@ assert array_slice_chars(xs, end, xs.length);
        //@ split_array_slice_chars(xs, start, end - 1, end);
        //@ assert array_slice_chars(xs, start, end - 1);
        //@ assert array_slice_chars(xs, end - 1, end);
        //@ close array_slice(xs, start, end);
        if (start >= end - 1)
            return;
        //@ open array_slice_chars(xs, end - 1, end);
        byte last = xs[end - 1];
        //@ close array_slice_chars(xs, end - 1, end);
        //@ close array_slice(xs, start, end);
        //@ assert array_slice(xs, start, end);
        //@ loop_invariant start <= i &*& i <= end - 1;
        //@ loop_invariant array_slice(xs, start, end);
        for (short i = start; i < end - 1; i++)

        {
            //@ open array_slice(xs, start, end);
            //@ split_array_slice_chars(xs, start, i, end);
            //@ assert array_slice_chars(xs, start, i);
            //@ assert array_slice_chars(xs, i, i + 1);
            //@ assert array_slice_chars(xs, i + 1, end);
            //@ open array_slice_chars(xs, i, i + 1);
            byte tmp = xs[i];
            //@ close array_slice_chars(xs, i, i + 1);
            //@ open array_slice_chars(xs, i + 1, i + 2);
            xs[i + 1] = tmp;
            //@ close array_slice_chars(xs, i + 1, i + 2);
            //@ merge_array_slice_chars(xs, start, i + 1, end);
            //@ close array_slice(xs, start, end);
        }
        //@ open array_slice(xs, start, end);
        //@ split_array_slice_chars(xs, start, start + 1, end);
        //@ assert array_slice_chars(xs, start, start + 1);
        //@ assert array_slice_chars(xs, start + 1, end);
        //@ open array_slice_chars(xs, start, start + 1);
        xs[start] = last;
        //@ close array_slice_chars(xs, start, start + 1);
        //@ merge_array_slice_chars(xs, start, end, xs.length);
        //@ merge_array_slice_chars(xs, 0, start, xs.length);
        //@ close array_slice(xs, 0, xs.length);
    }

    //@ lemma void split_array_slice_chars(byte[] a, int from, int mid, int to);
    //@ requires array_slice_chars(a, from, to) &*& from <= mid &*& mid <= to;
    //@ ensures array_slice_chars(a, from, mid) &*& array_slice_chars(a, mid, to);

    //@ lemma void merge_array_slice_chars(byte[] a, int from, int mid, int to);
    //@ requires array_slice_chars(a, from, mid) &*& array_slice_chars(a, mid, to);
    //@ ensures array_slice_chars(a, from, to);
}