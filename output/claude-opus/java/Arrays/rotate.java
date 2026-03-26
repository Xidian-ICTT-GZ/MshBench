class Program {
    //@ requires xs != null &*& xs.length > 0 &*& 0 <= start &*& start < end &*& end <= xs.length &*& array_slice(xs, 0, xs.length, _);
    //@ ensures array_slice(xs, 0, xs.length, _);
    static void rotate(byte[] xs, short start, short end)

    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ assert array_slice(xs, 0, xs.length, _);
        for (short i = start; i < end - 1; i++)
        //@ invariant array_slice(xs, 0, xs.length, _) &*& start <= i &*& i <= end - 1;
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}