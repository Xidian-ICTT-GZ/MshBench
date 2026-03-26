class Program {
    /*@
    predicate array_bytes(byte[] xs, int length) = length == xs.length;
    @*/
    
    static void rotate(byte[] xs, short start, short end)
        //@ requires array_bytes(xs, xs.length) &*& 0 <= start &*& start <= end &*& end <= xs.length;
        //@ ensures array_bytes(xs, xs.length);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ int i = start;
        for (short i = start; i < end - 1; i++)
            //@ invariant array_bytes(xs, xs.length) &*& start <= i &*& i < end - 1;
        {
            xs[i + 1] = xs[i];
            //@ i++;
        }
        xs[start] = last;
    }
}