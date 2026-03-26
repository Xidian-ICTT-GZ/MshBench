class Program {
    /*@ predicate dummy() = true; @*/

    //@ requires x != java.lang.Short.MIN_VALUE;
    //@ ensures result >= 0 &*& result == (x >= 0 ? x : -x);
    static short abs(short x)
    {
        if (x < 0) {
            x = (short) -x;
            return x;
        } else {
            return x;
        }
    }
}