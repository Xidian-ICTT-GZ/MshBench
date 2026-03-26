class Program {
    /*@ predicate array_slice(byte[] xs, int start, int end, list<byte> vs) = 
        start <= end &*& [1/2]xs |-> ?vs0 &*& length(vs0) == xs.length &*& 
        sublist(vs, vs0, start, end); @*/

    //@ requires xs != null &*& 0 <= start &*& start < end &*& end <= xs.length &*& xs.length < 32768;
    //@ requires array_slice(xs, 0, xs.length, ?vs);
    //@ ensures array_slice(xs, 0, xs.length, _);
    static void rotate(byte[] xs, short start, short end)
    {
        if (start >= end - 1)
            return;
        //@ open array_slice(xs, 0, xs.length, vs);
        byte last = xs[end - 1];
        short i = start;
        //@ loop_invariant start <= i &*& i <= end - 1 &*& array_slice(xs, 0, xs.length, vs) &*& xs[end - 1] == last;
        while (i < end - 1)
        {
            xs[i + 1] = xs[i];
            i++;
        }
        xs[start] = last;
        //@ close array_slice(xs, 0, xs.length, vs);
    }
}