/*@ predicate array_slice(byte[] a, int start, int end; byte[] contents) =
    start <= end &*&
    a != null &*&
    a.length >= end &*&
    chars(a, start, end - start, contents)
@*/

class Program {
    //@ requires start <= end &*& end <= xs.length &*& 0 <= start &*& array_slice(xs, start, end, ?contents);
    //@ ensures array_slice(xs, start, end, ?rotated) &*& rotated == append(tail(contents), cons(head(contents), nil));
    static void rotate(byte[] xs, short start, short end) {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ assert array_slice(xs, start, end, ?pre_contents);
        //@ open array_slice(xs, start, end, pre_contents);
        //@ chars_split(xs, start, end - 1);
        for (short i = start; i < end - 1; i++)
            /*@
            invariant
                start <= i &*& i <= end - 1 &*&
                array_slice(xs, start, i, ?left_part) &*&
                array_slice(xs, i, end - 1, ?right_part) &*&
                array_slice(xs, end - 1, end, ?last_part) &*&
                pre_contents == append(left_part, append(right_part, last_part)) &*&
                last_part == cons(last, nil);
            @*/
        {
            xs[i + 1] = xs[i];
            //@ open array_slice(xs, i, end - 1, ?right_rest);
            //@ chars_split(xs, i, i + 1);
            //@ open array_slice(xs, i, i + 1, ?curr_byte);
            //@ close array_slice(xs, i + 1, i + 2, curr_byte);
            //@ chars_merge(xs, i + 1, end - 1);
            //@ close array_slice(xs, i + 1, end - 1, right_rest);
        }
        xs[start] = last;
        //@ open array_slice(xs, start, start, _);
        //@ close array_slice(xs, start, start + 1, cons(last, nil));
        //@ chars_merge(xs, start, end);
        //@ close array_slice(xs, start, end, append(tail(pre_contents), cons(head(pre_contents), nil)));
    }
}