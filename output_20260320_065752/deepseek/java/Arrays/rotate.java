class Program {
    /*@
    predicate array_slice(byte[] xs, int start, int end) =
        start >= 0 &*& end <= xs.length &*& start <= end &*&
        array_slice_elems(xs, start, end);
    predicate array_slice_elems(byte[] xs, int start, int end) =
        start == end ? true : xs[start] |-> _ &*& array_slice_elems(xs, start + 1, end);
    @*/

    //@ requires array_slice(xs, start, end);
    //@ ensures array_slice(xs, start, end);
    static void rotate(byte[] xs, short start, short end)
        
        
    {
        //@ open array_slice(xs, start, end);
        //@ open array_slice_elems(xs, start, end);
        if (start >= end - 1) {
            //@ close array_slice_elems(xs, start, end);
            //@ close array_slice(xs, start, end);
            return;
        }
        //@ assert start < end - 1;
        //@ close array_slice_elems(xs, start, end);
        //@ close array_slice(xs, start, end);
        //@ array_slice_split(xs, start, end - 1);
        //@ array_slice_split(xs, end - 1, end);
        //@ open array_slice(xs, end - 1, end);
        //@ open array_slice_elems(xs, end - 1, end);
        byte last = xs[end - 1];
        //@ close array_slice_elems(xs, end - 1, end);
        //@ close array_slice(xs, end - 1, end);
        //@ array_slice_merge(xs, start, end - 1);
        //@ assert array_slice(xs, start, end - 1);
        //@ loop_invariant start <= i &*& i <= end - 1;
        //@ loop_invariant array_slice(xs, start, i);
        //@ loop_invariant array_slice(xs, i, end - 1);
        for (short i = start; i < end - 1; i++)
            
        {
            //@ array_slice_split(xs, i, i + 1);
            //@ open array_slice(xs, i, i + 1);
            //@ open array_slice_elems(xs, i, i + 1);
            xs[i + 1] = xs[i];
            //@ close array_slice_elems(xs, i, i + 1);
            //@ close array_slice(xs, i, i + 1);
            //@ array_slice_merge(xs, start, i + 1);
        }
        //@ array_slice_split(xs, start, start + 1);
        //@ open array_slice(xs, start, start + 1);
        //@ open array_slice_elems(xs, start, start + 1);
        xs[start] = last;
        //@ close array_slice_elems(xs, start, start + 1);
        //@ close array_slice(xs, start, start + 1);
        //@ array_slice_merge(xs, start, end);
    }

    /*@
    lemma void array_slice_split(byte[] xs, int split, int end)
        requires array_slice(xs, split, end) &*& split <= end;
        ensures array_slice(xs, split, split) &*& array_slice(xs, split, end);
    {
        open array_slice(xs, split, end);
        open array_slice_elems(xs, split, end);
        if (split == end) {
            close array_slice_elems(xs, split, split);
            close array_slice(xs, split, split);
            close array_slice_elems(xs, split, end);
            close array_slice(xs, split, end);
        } else {
            close array_slice_elems(xs, split, split);
            close array_slice(xs, split, split);
            array_slice_split(xs, split + 1, end);
            close array_slice_elems(xs, split, end);
            close array_slice(xs, split, end);
        }
    }

    lemma void array_slice_merge(byte[] xs, int start, int mid)
        requires array_slice(xs, start, mid) &*& array_slice(xs, mid, mid);
        ensures array_slice(xs, start, mid);
    {
        open array_slice(xs, start, mid);
        open array_slice_elems(xs, start, mid);
        if (start == mid) {
            close array_slice_elems(xs, start, mid);
            close array_slice(xs, start, mid);
        } else {
            array_slice_merge(xs, start + 1, mid);
            close array_slice_elems(xs, start, mid);
            close array_slice(xs, start, mid);
        }
    }
    @*/
}