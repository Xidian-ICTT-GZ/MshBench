class Program {
    //@ predicate array_range(byte[] xs, int start, int end) = 
    //     0 <= start &*& start <= end &*& end <= length(xs);
    //@ predicate rotated_array(byte[] xs, int start, int end) =
    //     array_range(xs, start, end) &*&
    //     exists(int i; 0 <= i &*& i < end - start;
    //         forall(int j; start <= j &*& j < end;
    //             xs[j] == xs[(start + ((j - start + i) % (end - start))) % end]))
    //     &*& end - start > 0;

    static void rotate(byte[] xs, short start, short end)
        //@ requires array_range(xs, start, end) &*& end - start >= 0;
        //@ ensures array_range(xs, start, end) &*&
        //           (end - start <= 1 ==> xs == xs) &*&
        //           (end - start > 1 ==> rotated_array(xs, start, end));
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        //@ loop_invariant array_range(xs, start, end) &*&
        //                0 <= i &*& i <= end - 1 &*&
        //                forall(int j; start <= j &*& j < i;
        //                    xs[j + 1] == xs_old[j]) &*&
        //                forall(int j; i <= j &*& j < end - 1;
        //                    xs[j + 1] == xs_old[j + 1]) &*&
        //                xs[start] == last;
        for (short i = start; i < end - 1; i++)
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}