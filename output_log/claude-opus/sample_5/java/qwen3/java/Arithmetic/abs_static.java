class Program {
    /*@ predicate is_short(int x) = x >= -32768 &*& x <= 32767; @*/

    static short abs(short x)
    //@ requires is_short(x);
    //@ ensures result >= 0 &*& (x >= 0 ==> result == x) &*& (x < 0 ==> result == -x);
    {
        if (x < 0) {
            x = (short) -x;
            return x;
        } else {
            return x;
        }
    }
}