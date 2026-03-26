class Program {
    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null &*& array_slice(xs, 0, xs.length, _) &*& 0 <= start &*& start <= end &*& end <= xs.length &*& xs.length <= Short.MAX_VALUE;
        //@ ensures array_slice(xs, 0, xs.length, _);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ requires array_slice(xs, 0, xs.length, _) &*& start <= i &*& i <= end - 1 &*& end <= xs.length;
            //@ ensures array_slice(xs, 0, xs.length, _);
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}