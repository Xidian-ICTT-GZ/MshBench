class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static short abs(short x)
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}