class Program {
    //@ requires x > Short.MIN_VALUE || x == 0;
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