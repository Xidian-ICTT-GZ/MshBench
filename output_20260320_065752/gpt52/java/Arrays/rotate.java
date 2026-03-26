class Program {
    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length;
        //@ ensures true;
        
        
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ invariant xs != null &*& 0 <= start &*& start <= i &*& i <= end - 1 &*& end <= xs.length;
            
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}