class Program {
    /*@ predicate bytes_slice(byte[] xs, int from, int to) =
            xs != null
        &*& 0 <= from
        &*& from <= to
        &*& to <= xs.length
        &*& array_slice(xs, from, to, _);
    @*/

    //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length &*& bytes_slice(xs, start, end);
    //@ ensures bytes_slice(xs, start, end);
    static void rotate(byte[] xs, short start, short end)
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
        //@ invariant xs != null &*& start <= i &*& i <= end - 1 &*& 0 <= start &*& start <= end &*& end <= xs.length &*& bytes_slice(xs, start, end);
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}