class Program {
    /*@
    predicate array_slice(byte[] xs, int from, int to) =
        from <= to &*& to <= xs.length &*& xs[from..to] |-> ?elems;
    @*/
    
    static void rotate(byte[] xs, short start, short end)
        //@ requires array_slice(xs, 0, xs.length) &*& 0 <= start &*& start <= end &*& end <= xs.length;
        //@ ensures array_slice(xs, 0, xs.length);
    {
        //@ open array_slice(xs, 0, xs.length);
        //@ assert xs[0..xs.length] |-> ?elems;
        if (start >= end - 1)
            //@ close array_slice(xs, 0, xs.length);
            return;
        //@ short end_minus_one = (short)(end - 1);
        //@ assert end_minus_one == end - 1;
        byte last = xs[end - 1];
        //@ short loop_start = start;
        //@ short loop_end = (short)(end - 1);
        //@ loop_invariant loop_start <= i &*& i <= loop_end;
        //@ loop_invariant array_slice(xs, 0, xs.length);
        for (short i = start; i < end - 1; i++)
            
        {
            //@ open array_slice(xs, 0, xs.length);
            //@ assert xs[0..xs.length] |-> ?current_elems;
            xs[i + 1] = xs[i];
            //@ close array_slice(xs, 0, xs.length);
        }
        //@ open array_slice(xs, 0, xs.length);
        xs[start] = last;
        //@ close array_slice(xs, 0, xs.length);
    }
}