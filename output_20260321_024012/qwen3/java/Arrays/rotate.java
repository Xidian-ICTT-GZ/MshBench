class Program {
    /*@
    predicate array_slice(byte[] a, int start, int end) =
        start <= end &*&
        a != null &*&
        a.length >= end &*&
        chars(a, _, _);
    @*/

    static void rotate(byte[] xs, short start, short end)
    //@ requires array_slice(xs, start, end);
    //@ ensures array_slice(xs, start, end);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ open array_slice(xs, start, end);
        for (short i = start; i < end - 1; i++)
        //@ invariant array_slice(xs, start, end) &*& i >= start &*& i <= end - 1;
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
        //@ close array_slice(xs, start, end);
    }
}