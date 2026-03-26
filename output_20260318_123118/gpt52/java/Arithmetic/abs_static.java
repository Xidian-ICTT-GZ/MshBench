class Program {
    static short abs(short x)
    //@ requires x != (short)-32768;
    //@ ensures true;
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}