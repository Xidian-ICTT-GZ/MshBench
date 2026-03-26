class Program {
    /*@
    predicate array_byte(byte[] xs, int lo, int hi) =
        lo >= hi ? emp :
        xs |-> ?arr &*& arr != null &*& 0 <= lo &*& lo < hi &*& array_byte(xs, lo + 1, hi);
    @*/
    
    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length &*& array_byte(xs, 0, xs.length);
        //@ ensures array_byte(xs, 0, xs.length);
    {
        if (start >= end - 1)
            return;
        //@ open array_byte(xs, 0, xs.length);
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ invariant start <= i &*& i < end - 1 &*& array_byte(xs, 0, xs.length);
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
        //@ close array_byte(xs, 0, xs.length);
    }
}