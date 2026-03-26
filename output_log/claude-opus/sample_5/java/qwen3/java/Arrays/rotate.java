class Program {
    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length &*& array_slice(xs, start, end, _);
        //@ ensures array_slice(xs, start, end, _);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ loop_invariant xs != null &*& 0 <= start &*& start <= i &*& i <= end - 1 &*& end <= xs.length &*& array_slice(xs, start, end, _);
        for (short i = (short)(end - 2); i >= start; i = (short)(i - 1))
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}