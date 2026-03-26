class Program {
    static short abs(short x)
    //@ requires x != Short.MIN_VALUE;
    //@ ensures (x < 0 ==> result == (short)-x) &*& (0 <= x ==> result == x);
    {
        if (x < 0) {
            x = (short) -x;
            return x;
        } else {
            return x;
        }
    }
}