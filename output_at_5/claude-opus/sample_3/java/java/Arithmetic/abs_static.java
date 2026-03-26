class Program {
    static short abs(short x)
    //@ requires true;
    //@ ensures -32768 <= result && result <= 32767 &*& (result == x || result == (short)-x) &*& (x < 0 ? result == (short)-x : result == x);
    {
        if (x < 0) {
            //@ assume x > Short.MIN_VALUE;
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}