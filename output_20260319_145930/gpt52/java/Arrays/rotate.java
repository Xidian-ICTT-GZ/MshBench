class Program {
    static void rotate(byte[] xs, short start, short end)
    //@ requires xs != null &*& array_slice(xs, 0, xs.length, _);
    //@ ensures array_slice(xs, 0, xs.length, _);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
        //@ invariant array_slice(xs, 0, xs.length, _);
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}