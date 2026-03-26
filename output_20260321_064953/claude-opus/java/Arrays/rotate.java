class Program {
    /*@
    predicate array_bytes(byte[] xs, int length) = length >= 0 &*& length <= xs.length &*& true;
    @*/
    static void rotate(byte[] xs, short start, short end)
        //@ requires array_bytes(xs, xs.length) &*& 0 <= start &*& start < end &*& end <= xs.length;
        //@ ensures array_bytes(xs, xs.length);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ invariant start <= i &*& i < end - 1 &*& array_bytes(xs, xs.length);
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}