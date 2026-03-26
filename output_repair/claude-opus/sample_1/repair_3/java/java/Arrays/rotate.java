class Program {
    /*@ predicate array_slice(byte[] xs, int start, int end, list<byte> vs) = 
        start >= 0 &*& end >= start &*& end <= xs.length &*& 
        length(vs) == end - start; @*/
    
    //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length &*& array_slice(xs, 0, xs.length, _);
    //@ ensures array_slice(xs, 0, xs.length, _);
    static void rotate(byte[] xs, short start, short end)
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ loop_invariant start <= i &*& i <= end - 1 &*& array_slice(xs, 0, xs.length, _);
        for (short i = start; i < end - 1; i++)
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}