/*@ predicate array_range(int[] a, int l, int h) =
    (l <= h) &*&
    chars(a, 0, a.length * sizeof(int)) &*&
    (l == h ? true : (0 <= l &*& l < h &*& h <= a.length));
@*/

class CoincidenceCount {

    //@ requires xs != null &*& ys != null;
    //@ requires array_range(xs, 0, xs.length) &*& array_range(ys, 0, ys.length);
    //@ ensures result >= 0;
    public static int coincidenceCount(int[] xs, int[] ys)
    {
        int i = 0;
        int j = 0;
        int n = 0;
        //@ loop_invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& n >= 0;
        //@ loop_invariant array_range(xs, 0, xs.length) &*& array_range(ys, 0, ys.length);
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