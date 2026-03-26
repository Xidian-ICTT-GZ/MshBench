class Program {
    /*@ predicate dummy() = true; @*/

    //@ requires x != -32768 &*& true;
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