class Program {
    //@ requires emp &*& x != Short.MIN_VALUE;
    //@ ensures emp &*& result >= 0;
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