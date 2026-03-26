class Program {
    /*@ predicate short_value(short x) = true; @*/

    //@ requires true;
    //@ ensures (x < 0 &*& result == -x) || (x >= 0 &*& result == x);
    static int abs(short x)
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}