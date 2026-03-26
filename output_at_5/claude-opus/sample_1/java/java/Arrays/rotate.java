class Program {
    /*@
    predicate array_byte(byte[] a, int lo, int hi;) =
      lo <= hi &*& hi <= a.length &*&
      a != null &*&
      true;
    @*/
    static void rotate(byte[] xs, short start, short end)
        //@ requires array_byte(xs, 0, xs.length);
        //@ requires 0 <= start &*& start <= end &*& end <= xs.length;
        //@ ensures array_byte(xs, 0, xs.length);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ open array_byte(xs, 0, xs.length);
        for (short i = start; i < end - 1; i++)
            //@ invariant array_byte(xs, 0, xs.length) &*& start <= i &*& i < end - 1;
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
        //@ close array_byte(xs, 0, xs.length);
    }
}