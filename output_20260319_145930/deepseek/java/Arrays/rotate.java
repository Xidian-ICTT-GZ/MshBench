class Program {
    //@ predicate array_slice(byte[] xs, int start, int end) = start <= end &*& xs != null &*& array_slice(xs, start, end, 1);
    //@ predicate array_slice(byte[] xs, int start, int end, int count) = start == end ? true : xs[start] |-> _ &*& array_slice(xs, start + 1, end, count + 1);
    
    //@ requires array_slice(xs, start, end);
    //@ ensures array_slice(xs, start, end);
    static void rotate(byte[] xs, short start, short end)
        //@ requires array_slice(xs, start, end);
        //@ ensures array_slice(xs, start, end);
    {
        //@ open array_slice(xs, start, end);
        //@ open array_slice(xs, start, end, 1);
        if (start >= end - 1) {
            //@ close array_slice(xs, start, end, 1);
            //@ close array_slice(xs, start, end);
            return;
        }
        //@ assert start < end - 1;
        //@ close array_slice(xs, start, end, 1);
        //@ close array_slice(xs, start, end);
        
        //@ open array_slice(xs, end - 1, end);
        //@ open array_slice(xs, end - 1, end, 1);
        byte last = xs[end - 1];
        //@ close array_slice(xs, end - 1, end, 1);
        //@ close array_slice(xs, end - 1, end);
        
        //@ loop_invariant start <= i && i <= end - 1;
        //@ loop_invariant array_slice(xs, start, end);
        for (short i = start; i < end - 1; i++)
            //@ requires start <= i && i <= end - 1;
            //@ requires array_slice(xs, start, end);
            //@ ensures array_slice(xs, start, end);
        {
            //@ open array_slice(xs, start, end);
            //@ open array_slice(xs, start, end, 1);
            //@ open array_slice(xs, i, i + 1);
            //@ open array_slice(xs, i, i + 1, 1);
            xs[i + 1] = xs[i];
            //@ close array_slice(xs, i, i + 1, 1);
            //@ close array_slice(xs, i, i + 1);
            //@ close array_slice(xs, start, end, 1);
            //@ close array_slice(xs, start, end);
        }
        
        //@ open array_slice(xs, start, end);
        //@ open array_slice(xs, start, end, 1);
        //@ open array_slice(xs, start, start + 1);
        //@ open array_slice(xs, start, start + 1, 1);
        xs[start] = last;
        //@ close array_slice(xs, start, start + 1, 1);
        //@ close array_slice(xs, start, start + 1);
        //@ close array_slice(xs, start, end, 1);
        //@ close array_slice(xs, start, end);
    }
}