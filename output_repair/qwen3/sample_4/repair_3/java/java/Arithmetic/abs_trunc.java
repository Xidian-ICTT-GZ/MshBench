class Program {
    /*@ predicate true_pred() = true; @*/

    //@ requires x != -32768;
    //@ ensures result >= 0 &*& result == (x < 0 ? -x : x);
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