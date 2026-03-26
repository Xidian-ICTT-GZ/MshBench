class Program {
    /*@
    predicate array_byte(byte[] a, int lo, int hi) =
        a != null &*& 0 <= lo &*& lo <= hi &*& hi <= a.length;
    @*/
    static void rotate(byte[] xs, short start, short end)
        //@ requires array_byte(xs, 0, xs.length) &*& 0 <= start &*& start <= end &*& end <= xs.length;
        //@ ensures array_byte(xs, 0, xs.length);
    {
        if (start >= end - 1)
            return;
        //@ open array_byte(xs, 0, xs.length);
        byte last = xs[end - 1];
        //@ short i = start;
        for (short i = start; i < end - 1; i++)
            /*@
            invariant array_byte(xs, 0, xs.length) &*& start <= i &*& i < end - 1;
            @*/
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
        //@ close array_byte(xs, 0, xs.length);
    }
}