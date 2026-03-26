class Program {
    /*@ predicate array_slice(byte[] xs, int start, int end, list<byte> vs) =
        [_]xs |-> ?vs0 &*& vs == take(end - start, drop(start, vs0)); @*/

    static void rotate(byte[] xs, short start, short end)
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}