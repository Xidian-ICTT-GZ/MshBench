class Program {
    /*@ predicate dummy() = true; @*/

    //@ requires x >= -32767;
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