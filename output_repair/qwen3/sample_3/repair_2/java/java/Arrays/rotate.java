class Program {
    /*@ predicate array_slice(byte[] xs, int start, int end, list<byte> vs;) = 
        start <= end &*& [?f]xs |-> ?vs0 &*& vs == take(end - start, drop(start, vs0)); @*/

    //@ requires xs != null &*& 0 <= start &*& start < end &*& end <= xs.length &*& xs.length < 32768;
    //@ requires array_slice(xs, 0, xs.length, _);
    //@ ensures array_slice(xs, 0, xs.length, _);
    static void rotate(byte[] xs, short start, short end) {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ loop_invariant start <= i &*& i <= end - 1 &*& array_slice(xs, 0, xs.length, _);
        for (short i = start; i < end - 1; i++) {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}