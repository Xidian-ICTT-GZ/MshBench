class Program {
    /*@ predicate array_slice(byte[] xs, int start, int end, list<byte> vs) =
        start <= end &*& [?f]xs |-> ?vs0 &*& vs == take(end - start, drop(start, vs0)); @*/

    //@ requires xs != null &*& 0 <= start &*& start < end &*& end <= xs.length &*& xs.length < 32768;
    //@ requires array_slice(xs, 0, xs.length, ?vs);
    //@ ensures array_slice(xs, 0, xs.length, ?vs1) &*& vs1 == cons(last(vs), drop(1, vs));
    static void rotate(byte[] xs, short start, short end) {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ open array_slice(xs, 0, xs.length, _);
        //@ assert [?f]xs |-> ?vs0;
        //@ close array_slice(xs, 0, xs.length, vs0);
        //@ loop_invariant start <= i &*& i <= end - 1 &*& [f]xs |-> vs0;
        for (short i = start; i < end - 1; i++) {
            xs[i + 1] = xs[i];
            //@ vs0 = update(vs0, i + 1, nth(i, vs0));
        }
        xs[start] = last;
        //@ vs0 = update(vs0, start, last);
        //@ close array_slice(xs, 0, xs.length, vs0);
    }
}