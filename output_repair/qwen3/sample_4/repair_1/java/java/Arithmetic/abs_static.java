class Program {
    /*@ predicate dummy() = true; @*/

    //@ requires x != Short.MIN_VALUE &*& true;
    //@ ensures result >= 0 &*& true;
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