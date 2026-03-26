/*@ predicate array_slice(byte[] a, int start, int end; byte v) =
    start <= end &*&
    chars(a, _, ?cs) &*&
    sublist(cs, start, end, ?sub) &*&
    sub == repeat(end - start, v);
@*/

/*@ predicate array_content(byte[] a, int start, int end; list<byte> content) =
    start <= end &*&
    chars(a, _, ?cs) &*&
    sublist(cs, start, end, content);
@*/

class Program {
    //@ requires chars(xs, ?n, ?cs) &*& 0 <= start &*& start <= end &*& end <= n;
    //@ ensures chars(xs, n, ?cs1) &*&
    
    
    
    
    
    
    
    
    
    
    static void rotate(byte[] xs, short start, short end) {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ open chars(xs, _, _);
        //@ assert chars(xs, ?n, ?cs);
        //@ assert nth(end - 1, cs, last);
        //@ close chars(xs, n, cs);
        for (short i = start; i < end - 1; i++)
            /*@
                invariant chars(xs, n, ?cs_i) &*&
                          start <= i &*& i <= end - 1 &*&
                          sublist(cs, start, i, ?moved) &*&
                          sublist(cs_i, start + 1, i + 1, moved) &*&
                          nth(end - 1, cs, last) &*&
                          sublist(cs_i, start + (i - start) + 1, end, sublist(cs, i + 1, end, _)) &*&
                          sublist(cs_i, 0, start, sublist(cs, 0, start, _));
            @*/
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}