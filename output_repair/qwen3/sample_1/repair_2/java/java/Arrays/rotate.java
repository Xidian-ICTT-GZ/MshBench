class Program {
    /*@ predicate array_slice(byte[] xs, int start, int end, list<byte> vs) =
        [_]xs |-> ?vs0 &*& vs == take(end - start, drop(start, vs0)); @*/

    //@ requires xs != null &*& 0 <= start &*& start < end &*& end <= xs.length &*& xs.length < 32768;
    //@ requires array_slice(xs, 0, xs.length, ?old_contents);
    //@ ensures array_slice(xs, 0, xs.length, ?new_contents) &*&
    //@         new_contents == cons(last(old_contents), take(end - start - 1, drop(start, old_contents))) ++ drop(end - start, old_contents);
    static void rotate(byte[] xs, short start, short end)
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ open array_slice(xs, 0, xs.length, _);
        //@ assert [_]xs |-> ?full;
        //@ close array_slice(xs, 0, xs.length, full);
        //@ loop_invariant start <= i &*& i <= end - 1 &*& [_]xs |-> ?vs &*&
        //@   array_slice(xs, 0, xs.length, vs) &*&
        //@   take(i - start + 1, drop(start, vs)) == take(i - start + 1, drop(start, full)) &*&
        //@   drop(i - start + 1, drop(start, vs)) == drop(i - start + 1, drop(start, full));
        for (short i = start; i < end - 1; i++)
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}