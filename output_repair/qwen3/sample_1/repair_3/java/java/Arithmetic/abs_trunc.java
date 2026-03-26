class Program {
    //@ requires emp;
    //@ ensures emp &*& (x >= 0 ? result == x : result == -x) &*& result >= 0;
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