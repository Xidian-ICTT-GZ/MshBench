class Program {
    /*@
    predicate array_slice(byte[] xs, int start, int end) =
        start >= 0 &*& end >= start &*& end <= xs.length &*&
        array_slice(xs, start, end, _);
    predicate array_slice(byte[] xs, int start, int end, list<byte> elems);
    @*/

    //@ requires array_slice(xs, start, end);
    //@ ensures array_slice(xs, start, end);
    static void rotate(byte[] xs, short start, short end)
        
        
    {
        //@ open array_slice(xs, start, end);
        //@ assert array_slice(xs, start, end, ?elems);
        if (start >= end - 1)
            //@ close array_slice(xs, start, end);
            return;
        //@ short end_minus_one = (short)(end - 1);
        //@ split_array_slice(xs, start, end_minus_one, end);
        //@ assert array_slice(xs, end_minus_one, end, ?last_elem_list);
        //@ close array_slice_chars(xs, end_minus_one, end);
        byte last = xs[end - 1];
        //@ open array_slice_chars(xs, end_minus_one, end);
        //@ merge_array_slice(xs, start, end_minus_one, end);
        //@ short i = start;
        //@ close array_slice(xs, start, start);
        //@ close foreach(start, i, xs, start, end);
        for (short i = start; i < end - 1; i++)
            //@ invariant start <= i &*& i <= end - 1 &*& array_slice(xs, start, i) &*& array_slice(xs, i, end) &*& foreach(start, i, xs, start, end);
            
        {
            //@ open foreach(start, i, xs, start, end);
            //@ short next = (short)(i + 1);
            //@ split_array_slice(xs, i, next, end);
            //@ assert array_slice(xs, i, next, ?cur_elem_list);
            //@ close array_slice_chars(xs, i, next);
            //@ open array_slice_chars(xs, i, next);
            xs[i + 1] = xs[i];
            //@ close array_slice_chars(xs, i, next);
            //@ open array_slice_chars(xs, i, next);
            //@ merge_array_slice(xs, i, next, end);
            //@ close foreach(start, (short)(i + 1), xs, start, end);
        }
        //@ open foreach(start, (short)(end - 1), xs, start, end);
        //@ split_array_slice(xs, start, (short)(start + 1), end);
        //@ assert array_slice(xs, start, (short)(start + 1), ?first_slice);
        //@ close array_slice_chars(xs, start, (short)(start + 1));
        //@ open array_slice_chars(xs, start, (short)(start + 1));
        xs[start] = last;
        //@ close array_slice_chars(xs, start, (short)(start + 1));
        //@ open array_slice_chars(xs, start, (short)(start + 1));
        //@ merge_array_slice(xs, start, (short)(start + 1), end);
        //@ close array_slice(xs, start, end);
    }

    /*@
    predicate foreach(short start, short i, byte[] xs, short slice_start, short slice_end) =
        i == slice_end ?
            true
        :
            i >= start &*&
            (i == start ?
                true
            :
                foreach(start, (short)(i - 1), xs, slice_start, slice_end)
            ) &*&
            array_slice_chars(xs, i, (short)(i + 1));

    predicate array_slice_chars(byte[] xs, int from, int to) =
        from >= 0 &*& to == from + 1 &*& to <= xs.length &*&
        xs[from] |-> ?v &*&
        array_slice_chars_fp(xs, from, to, v);
    predicate_family array_slice_chars_fp(byte[] xs, int from, int to, byte v);

    lemma void split_array_slice(byte[] xs, int split_start, int split_mid, int split_end);
        requires array_slice(xs, split_start, split_end, ?elems) &*& split_start <= split_mid &*& split_mid <= split_end;
        ensures array_slice(xs, split_start, split_mid, take(split_mid - split_start, elems)) &*& array_slice(xs, split_mid, split_end, drop(split_mid - split_start, elems));

    lemma void merge_array_slice(byte[] xs, int merge_start, int merge_mid, int merge_end);
        requires array_slice(xs, merge_start, merge_mid, ?elems1) &*& array_slice(xs, merge_mid, merge_end, ?elems2);
        ensures array_slice(xs, merge_start, merge_end, append(elems1, elems2));
    @*/
}