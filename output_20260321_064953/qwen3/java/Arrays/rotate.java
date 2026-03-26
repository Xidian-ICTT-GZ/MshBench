class Program {
    /*@
    predicate array_slice(byte[] arr, int start, int end) =
        arr != null &*&
        0 <= start &*& start <= end &*& end <= arr.length &*&
        chars(arr, start, end - start, _);
    @*/

    static void rotate(byte[] xs, short start, short end)
    //@ requires array_slice(xs, start, end);
    //@ ensures array_slice(xs, start, end);
    {
        if (start >= end - 1)
            return;
        //@ open array_slice(xs, start, end);
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
        //@ invariant array_slice(xs, start, end) &*& i >= start &*& i <= end - 1;
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
        //@ close array_slice(xs, start, end);
    }
}