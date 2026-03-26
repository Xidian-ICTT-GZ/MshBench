class Program {
    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length &*& array_slice(xs, 0, xs.length, _);
        //@ ensures array_slice(xs, 0, xs.length, _);
        
        
    {
        //@ open array_slice(xs, 0, xs.length, _);
        if (start >= end - 1) {
            //@ close array_slice(xs, 0, xs.length, _);
            return;
        }
        byte last = xs[end - 1];
        //@ assert 0 <= end - 1 &*& end - 1 < xs.length;
        for (short i = start; i < end - 1; i++)
            //@ invariant start <= i &*& i <= end - 1 &*& 0 <= start &*& start <= end &*& end <= xs.length;
            
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
        //@ close array_slice(xs, 0, xs.length, _);
    }
}