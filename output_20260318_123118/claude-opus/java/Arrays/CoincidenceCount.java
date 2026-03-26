class CoincidenceCount {

    /*@ 
    predicate array_int(int[] a, int length) = 
        a != null &*& length >= 0 &*& fraction(1.0) &*&
        a.length == length &*&
        integer(a, 0, length);
    @*/
    
    /*@
    predicate integer(int[] a, int start, int end) = 
        start == end ? emp : (a[start] |-> _) &*& integer(a, start + 1, end);
    @*/

    //@ requires array_int(xs, xs.length) &*& array_int(ys, ys.length);
    //@ ensures array_int(xs, xs.length) &*& array_int(ys, ys.length) &*& 0 <= result &*& result <= xs.length &*& result <= ys.length;
    public static int coincidenceCount(int[] xs, int[] ys)
    {
        int i = 0;
        int j = 0;
        int n = 0;
        /*@
        loop_invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& 0 <= n &*& n <= i &*& n <= j &*&
            array_int(xs, xs.length) &*& array_int(ys, ys.length);
        @*/
        for (;;)
        {
            if (i == xs.length) {
                break;
            }
            if (j == ys.length) {
                break;
            }
            if (xs[i] < ys[j]) {
                i++;
            } else if (xs[i] > ys[j]) {
                j++;
            } else {
                n++;
                i++;
                j++;
            }
        }
        return n;
    }
}