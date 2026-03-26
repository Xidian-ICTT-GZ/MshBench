class Program {
    /*@
    predicate array_slice(byte[] xs, int start, int end) =
        start >= 0 &*& end <= xs.length &*& start <= end &*&
        array_slice(xs, start, end, _);
    predicate array_slice(byte[] xs, int start, int end, list<byte> elems);
    @*/

    //@ requires array_slice(xs, start, end);
    //@ ensures array_slice(xs, start, end);
    static void rotate(byte[] xs, short start, short end)
        
        
    {
        //@ open array_slice(xs, start, end);
        //@ close array_slice(xs, start, end);
        if (start >= end - 1)
            //@ close array_slice(xs, start, end);
            return;
        //@ open array_slice(xs, start, end, _);
        byte last = xs[end - 1];
        //@ assert array_slice(xs, start, end - 1, ?elems);
        //@ close array_slice(xs, start, start, nil);
        for (short i = start; i < end - 1; i++)
            //@ invariant start <= i &*& i <= end - 1;
            //@ invariant array_slice(xs, start, i, ?elems1);
            //@ invariant array_slice(xs, i, end - 1, ?elems2);
            //@ invariant array_slice(xs, end - 1, end, cons(last, nil));
        {
            //@ open array_slice(xs, i, end - 1, _);
            xs[i + 1] = xs[i];
            //@ close array_slice(xs, i, i + 1, cons(xs[i], nil));
        }
        xs[start] = last;
        //@ close array_slice(xs, start, end, _);
    }
}