class Program {
    //@ requires emp &*& x != -32768;
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