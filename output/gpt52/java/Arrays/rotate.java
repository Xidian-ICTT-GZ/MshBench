class Program {
    /*@
    predicate bytes(byte[] a; int n) =
        a != null &*& a.length == n &*& 0 <= n &*&
        array_slice(a, 0, n, _);
    @*/

    static void rotate(byte[] xs, short start, short end)
    //@ requires bytes(xs, ?n) &*& 0 <= start &*& start <= end &*& end <= n &*& end - 1 <= 32767;
    //@ ensures bytes(xs, n);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
        //@ invariant bytes(xs, n) &*& start <= i &*& i <= end - 1;
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}