class Program {
    /*@ predicate array_slice(byte[] xs, int start, int end, list<byte> vs) = 
        start <= end &*& [1/2]xs |-> ?vs0 &*& length(vs0) == xs.length &*& 
        sublist(vs0, start, end, vs); @*/

    //@ requires xs != null &*& 0 <= start &*& start < end &*& end <= xs.length &*& xs.length < 32768;
    //@ requires array_slice(xs, 0, xs.length, ?vs);
    //@ ensures array_slice(xs, 0, xs.length, ?ws) &*& 
    //      sublist(vs, start, end - 1, ?mid) &*& 
    //      ws == take(start, vs) ++ cons(last(vs), mid) ++ drop(end, vs);
    static void rotate(byte[] xs, short start, short end)
    {
        if (start >= end - 1)
            return;
        //@ open array_slice(xs, 0, xs.length, _);
        byte last = xs[end - 1];
        short i = start;
        //@ close array_slice(xs, 0, xs.length, _);
        //@ loop_invariant start <= i &*& i <= end - 1 &*& array_slice(xs, 0, xs.length, ?vs_i) &*&
        //      take(start, vs_i) == take(start, vs) &*&
        //      drop(i + 1, vs_i) == drop(i + 1, vs) &*&
        //      sublist(vs, start, i, ?prefix) &*&
        //      sublist(vs_i, start + 1, i + 1, prefix);
        while (i < end - 1)
        {
            xs[i + 1] = xs[i];
            i++;
        }
        xs[start] = last;
    }
}