class Program {
    /*@
    predicate array_slice(byte[] xs; int from, int to) =
        from >= to ?
            true
        :
            java.lang.array_element(xs, from, _) &*& array_slice(xs, from + 1, to);
    @*/

    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length &*& array_slice(xs, start, end);
        //@ ensures xs != null &*& array_slice(xs, start, end);
        
        
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ invariant xs != null &*& 0 <= start &*& start <= i &*& i <= end - 1 &*& end <= xs.length &*& array_slice(xs, start, end);
            
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}