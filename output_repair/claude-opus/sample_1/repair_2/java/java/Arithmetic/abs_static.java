class Program {
    //@ requires x > -32768;
    //@ ensures result >= 0;
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