class Program {
    /*@
    predicate array_slice(byte[] arr, int start, int end; byte[] contents) =
        arr != null &*&
        start <= end &*&
        [1/2]arr |-> ?a &*&
        malloc_block(arr, a) &*&
        length(a) == length(contents) &*&
        true == ((start >= 0) && (end <= length(a))) &*&
        sublist(a, start, end) == sublist(contents, start, end);
    @*/

    //@ requires xs != null &*& [?f]xs |-> ?a &*& malloc_block(xs, a) &*& start >= 0 &*& end >= start &*& end <= length(a);
    //@ ensures [f]xs |-> a &*& malloc_block(xs, a);
    static void rotate(byte[] xs, short start, short end) {
        if (start >= end - 1)
            return;
        //@ open [f]xs |-> a;
        //@ assert malloc_block(xs, a);
        byte last = xs[end - 1];
        //@ close [f]xs |-> a;

        //@ open [f]xs |-> a;
        for (short i = start; i < end - 1; i++)
            //@ invariant [f]xs |-> a &*& malloc_block(xs, a) &*& start <= i &*& i <= end - 1;
        {
            xs[i + 1] = xs[i];
        }
        //@ close [f]xs |-> a;

        //@ open [f]xs |-> a;
        xs[start] = last;
        //@ close [f]xs |-> a;
    }
}