class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures result == (x < 0 ? (x == Short.MIN_VALUE ? x : (short)-x) : x);
    {
        if (x < 0) {
            return x == Short.MIN_VALUE ? x : (short)-x;
        } else {
            return x;
        }
    }
}