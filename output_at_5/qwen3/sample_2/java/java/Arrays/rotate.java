class Program {
    static void rotate(byte[] xs, short start, short end)
        //@ requires xs != null;
        //@ requires 0 <= start && start < xs.length;
        //@ requires 0 <= end && end <= xs.length;
        //@ requires start < end;
        //@ ensures true;
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ loop_invariant start <= i && i < end;
            //@ loop_invariant xs != null;
            //@ loop_invariant 0 <= i + 1 && i + 1 < xs.length;
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}