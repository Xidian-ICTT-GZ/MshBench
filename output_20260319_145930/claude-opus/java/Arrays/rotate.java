class Program {
    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null &*& 0 <= start &*& start <= end &*& end <= xs.length &*& array_slice(xs, start, end, _);
        //@ ensures array_slice(xs, start, end, _);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ invariant start <= i &*& i <= end - 1 &*& array_slice(xs, start, end, _);
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}